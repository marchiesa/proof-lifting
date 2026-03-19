#!/bin/bash
#SBATCH --job-name=quirk-bench
#SBATCH --output=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/quirk-bench_%j.out
#SBATCH --error=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/quirk-bench_%j.err
#SBATCH --time=02:00:00
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=128G
#SBATCH --partition=boost_usr_prod
#SBATCH --qos=normal
#SBATCH --account=EUHPC_D29_022
#SBATCH --gres=gpu:4

# --- Configuration ---
WORK="/leonardo_work/EUHPC_D29_022/mchiesa0"
MODEL="$WORK/models/gpt-oss-20b-hf"
Z3="$WORK/software/z3/bin/z3"
BENCHMARK_DIR="$WORK/benchmark"
INPUTS_DIR="$BENCHMARK_DIR/inputs"
RESULTS_DIR="$BENCHMARK_DIR/results_sglang_$(date +%Y%m%d_%H%M%S)"
PORT=8000
WORKERS=8  # concurrent problems — SGLang handles batching internally

set -e
module load python/3.11.7 cuda/12.3

source "$WORK/software/sglang_env/bin/activate"
export DOTNET8="$WORK/software/dotnet8/dotnet"
export DAFNY_DLL="$WORK/software/dafny-modified/Dafny.dll"
export Z3_PATH="$Z3"

mkdir -p "$RESULTS_DIR" "$WORK/logs"

echo "=== SMT Quirk Benchmark (SGLang) ==="
echo "Node: $(hostname)"
echo "GPUs: 4"
echo "Model: $MODEL"
echo "Workers: $WORKERS"
echo "Job ID: $SLURM_JOB_ID"
nvidia-smi --query-gpu=name,memory.total --format=csv
echo ""

# --- Start SGLang with tensor parallelism across 4 GPUs ---
echo "Starting SGLang server (4-GPU TP)..."
python -m sglang.launch_server \
    --model-path "$MODEL" \
    --host 127.0.0.1 \
    --port $PORT \
    --tp 4 \
    --mem-fraction-static 0.88 \
    --context-length 8192 \
    --max-running-requests 64 \
    --log-level warning \
    2>&1 &
SERVER_PID=$!

# Wait for server to be ready (SGLang has long startup)
echo "Waiting for server..."
for i in $(seq 1 180); do
    if curl -s "http://127.0.0.1:$PORT/health" > /dev/null 2>&1; then
        echo "Server ready after $((i * 10))s"
        break
    fi
    if ! kill -0 $SERVER_PID 2>/dev/null; then
        echo "ERROR: Server process died"
        exit 1
    fi
    sleep 10
done

if ! curl -s "http://127.0.0.1:$PORT/health" > /dev/null 2>&1; then
    echo "ERROR: Server not ready after 30 minutes"
    kill $SERVER_PID 2>/dev/null
    exit 1
fi

nvidia-smi --query-gpu=memory.used,memory.free --format=csv
echo ""

# --- Run benchmark ---
echo "Running benchmark..."
python3 "$BENCHMARK_DIR/run_benchmark.py" \
    --inputs-dir "$INPUTS_DIR" \
    --output-dir "$RESULTS_DIR" \
    --backend sglang \
    --url "http://127.0.0.1:$PORT" \
    --workers $WORKERS \
    --timeout 500

echo ""
echo "=== Benchmark complete ==="
echo "Results: $RESULTS_DIR"
cat "$RESULTS_DIR/summary.json"

# Cleanup
kill $SERVER_PID 2>/dev/null || true
