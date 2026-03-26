#!/bin/bash
#SBATCH --job-name=verus-test
#SBATCH --output=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/verus_test_%j.out
#SBATCH --error=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/verus_test_%j.err
#SBATCH --time=00:15:00
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=64G
#SBATCH --partition=boost_usr_prod
#SBATCH --qos=normal
#SBATCH --account=EUHPC_D29_022
#SBATCH --gres=gpu:4

# Quick test: llama.cpp + one Verus problem
# llama.cpp starts in seconds vs SGLang's 3+ minutes

set -e

WORK="/leonardo_work/EUHPC_D29_022/mchiesa0"
BENCHMARK_DIR="$WORK/benchmark_verus"
INPUTS_DIR="$BENCHMARK_DIR/inputs"
LLAMA_SERVER="$WORK/software/llama.cpp/build/bin/llama-server"
MODEL="$WORK/models/gpt-oss-20b-mxfp4.gguf"
PORT=8080

# Verus setup
export VERUS_BIN="$WORK/software/verus/verus-x86-linux/verus"
export VERUS_SIF="$WORK/software/verus/ubuntu_22.04.sif"
export CARGO_BIN="$WORK/software/cargo/bin"
export RUSTUP_HOME="$WORK/software/rustup"
export CARGO_HOME="$WORK/software/cargo"
export BENCHMARK_MODEL="gpt-oss-20b"
export BENCHMARK_CHAT_API="true"

module load python/3.11.7 cuda/12.3

mkdir -p "$WORK/logs"

echo "=== Verus Test (llama.cpp) ==="
echo "Node: $(hostname), Job: $SLURM_JOB_ID"
nvidia-smi --query-gpu=name,memory.total --format=csv
echo ""

# Test Verus works
echo "Testing Verus..."
singularity exec --bind /leonardo_work:/leonardo_work \
  --env PATH=$CARGO_BIN:$PATH \
  --env RUSTUP_HOME=$RUSTUP_HOME \
  --env CARGO_HOME=$CARGO_HOME \
  $VERUS_SIF $VERUS_BIN --version
echo ""

# Start llama.cpp server
echo "Starting llama.cpp server..."
$LLAMA_SERVER \
    -m "$MODEL" \
    --host 127.0.0.1 \
    --port $PORT \
    -ngl 99 \
    --ctx-size 8192 \
    2>&1 &
SERVER_PID=$!

# Wait for server (llama.cpp is fast — usually <30s)
for i in $(seq 1 60); do
    if curl -s "http://127.0.0.1:$PORT/health" > /dev/null 2>&1; then
        echo "Server ready after ${i}s"
        break
    fi
    if ! kill -0 $SERVER_PID 2>/dev/null; then
        echo "ERROR: Server died"
        exit 1
    fi
    sleep 1
done

if ! curl -s "http://127.0.0.1:$PORT/health" > /dev/null 2>&1; then
    echo "ERROR: Server not ready after 60s"
    kill $SERVER_PID 2>/dev/null
    exit 1
fi

# Run benchmark on one problem
RESULTS_DIR="$BENCHMARK_DIR/results/test_llama_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULTS_DIR"

echo ""
echo "Running benchmark on 5 problems..."
python3 "$BENCHMARK_DIR/run_benchmark_verus.py" \
    --inputs-dir "$INPUTS_DIR" \
    --output-dir "$RESULTS_DIR" \
    --backend llama \
    --url "http://127.0.0.1:$PORT" \
    --workers 1 \
    --timeout 120 \
    --names 0025_1096_A 0053_1230_A 0024_1091_A 0012_1060_A 0040_1159_A

echo ""
echo "=== Results ==="
cat "$RESULTS_DIR/summary.json" 2>/dev/null || echo "No summary"
echo ""
echo "=== Done ==="

kill $SERVER_PID 2>/dev/null || true
