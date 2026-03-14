#!/usr/bin/env bash
#
# SLURM batch script for running the Dafny verification benchmark on
# Leonardo (CINECA) with vLLM-served models on A100 GPUs.
#
# ─────────────────────────────────────────────────────────────────────
# HOW TO CUSTOMIZE
# ─────────────────────────────────────────────────────────────────────
#   1. Set MODEL to the HuggingFace model ID you want to evaluate.
#   2. Adjust --nodes / --ntasks / --gres to control GPU count.
#      Each task starts one vLLM server on one GPU.
#   3. Set --time according to your estimate of total wall-clock time.
#   4. BENCHMARK_DIR should point to the benchmark/ directory in this
#      repo after cloning onto the shared filesystem.
#   5. DAFNY_CMD should point to a working Dafny installation.
#
# ─────────────────────────────────────────────────────────────────────
# SUBMISSION
# ─────────────────────────────────────────────────────────────────────
#   sbatch leonardo_job.sh
#
# ─────────────────────────────────────────────────────────────────────

#SBATCH --job-name=dafny-bench
#SBATCH --partition=boost_usr_prod          # Leonardo GPU partition
#SBATCH --account=<YOUR_ACCOUNT>            # <<< CHANGE THIS
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=4                 # 4 GPUs per node on Leonardo
#SBATCH --gres=gpu:4
#SBATCH --cpus-per-task=8
#SBATCH --mem=480G                          # ~120 GB per GPU
#SBATCH --time=04:00:00
#SBATCH --output=slurm-%j.out
#SBATCH --error=slurm-%j.err

set -euo pipefail

# ── Configuration ────────────────────────────────────────────────────

MODEL="${MODEL:-meta-llama/Llama-3.1-70B-Instruct}"
BENCHMARK_DIR="${BENCHMARK_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
RESULTS_DIR="${RESULTS_DIR:-${BENCHMARK_DIR}/results/leonardo_$(date +%Y%m%d_%H%M%S)}"
DAFNY_CMD="${DAFNY_CMD:-dafny}"
MAX_ITERATIONS="${MAX_ITERATIONS:-20}"
TIMEOUT="${TIMEOUT:-600}"

# Number of GPUs available.
NUM_GPUS="${SLURM_NTASKS:-4}"

# vLLM port range (one server per GPU).
BASE_PORT=8000

# Tensor-parallel size per server.  For models that fit on one A100
# (<=40 GB weights), keep TP_SIZE=1 and run one server per GPU.
# For larger models (70B at fp16), set TP_SIZE=2 and halve NUM_GPUS.
TP_SIZE="${TP_SIZE:-1}"

echo "========================================"
echo " Dafny Verification Benchmark (Leonardo)"
echo "========================================"
echo "  Model:          $MODEL"
echo "  GPUs:           $NUM_GPUS"
echo "  TP size:        $TP_SIZE"
echo "  Benchmark dir:  $BENCHMARK_DIR"
echo "  Results dir:    $RESULTS_DIR"
echo "  Max iterations: $MAX_ITERATIONS"
echo "  Timeout:        $TIMEOUT s"
echo "========================================"

# ── Load modules ─────────────────────────────────────────────────────

module purge
module load cuda/12.1       2>/dev/null || true
module load python/3.11     2>/dev/null || true
module load gcc/12.2.0      2>/dev/null || true

# Activate virtualenv if present.
if [[ -f "${BENCHMARK_DIR}/../.venv/bin/activate" ]]; then
    source "${BENCHMARK_DIR}/../.venv/bin/activate"
fi

# ── Start vLLM servers ──────────────────────────────────────────────

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ENDPOINTS=""

effective_servers=$(( NUM_GPUS / TP_SIZE ))

for (( i=0; i<effective_servers; i++ )); do
    PORT=$(( BASE_PORT + i ))
    GPU_START=$(( i * TP_SIZE ))

    # Build a comma-separated GPU list for tensor parallelism.
    GPU_IDS="$GPU_START"
    for (( g=1; g<TP_SIZE; g++ )); do
        GPU_IDS="${GPU_IDS},$((GPU_START + g))"
    done

    echo "Starting vLLM server $i on GPU(s) $GPU_IDS, port $PORT ..."
    ENDPOINT=$("${SCRIPT_DIR}/launch_vllm.sh" "$MODEL" "$PORT" "$GPU_IDS" "$TP_SIZE")
    ENDPOINTS="${ENDPOINTS}${ENDPOINT}\n"
    echo "  -> $ENDPOINT"
done

# Pick the first endpoint for the benchmark runner.
# The parallel_runner will spray problems across the single endpoint
# (vLLM handles concurrent requests internally).
PRIMARY_ENDPOINT=$(echo -e "$ENDPOINTS" | head -1)

echo ""
echo "All vLLM servers running.  Primary endpoint: $PRIMARY_ENDPOINT"
echo ""

# ── Run the benchmark ────────────────────────────────────────────────

mkdir -p "$RESULTS_DIR"

python "${BENCHMARK_DIR}/parallel_runner.py" \
    --dataset "${BENCHMARK_DIR}/dataset/problems" \
    --adapter openai_compatible \
    --base-url "$PRIMARY_ENDPOINT" \
    --model "$MODEL" \
    --timeout "$TIMEOUT" \
    --max-iterations "$MAX_ITERATIONS" \
    --real-dafny "$DAFNY_CMD" \
    --output-dir "$RESULTS_DIR" \
    --workers "$effective_servers"

echo ""
echo "Benchmark complete.  Results in: $RESULTS_DIR"

# ── Cleanup: stop vLLM servers ───────────────────────────────────────

echo "Stopping vLLM servers..."
pkill -f "vllm.entrypoints.openai.api_server" || true

echo "Done."
