#!/bin/bash
#SBATCH --job-name=quirk-llama
#SBATCH --output=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/quirk-llama_%j.out
#SBATCH --error=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/quirk-llama_%j.err
#SBATCH --time=01:00:00
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=64G
#SBATCH --partition=boost_usr_prod
#SBATCH --qos=normal
#SBATCH --account=EUHPC_D29_022
#SBATCH --gres=gpu:1

# Quick test variant using llama.cpp (faster startup, 1 GPU, batch=1)
WORK="/leonardo_work/EUHPC_D29_022/mchiesa0"
MODEL="$WORK/models/gpt-oss-20b-mxfp4.gguf"
LLAMA_SERVER="$WORK/software/llama.cpp/build/bin/llama-server"
DAFNY="$WORK/software/dafny/dafny"
Z3="$WORK/software/z3/bin/z3"
BENCHMARK_DIR="$WORK/benchmark"
INPUTS_DIR="$BENCHMARK_DIR/inputs"
RESULTS_DIR="$BENCHMARK_DIR/results_llama_$(date +%Y%m%d_%H%M%S)"
PORT=$((8000 + (SLURM_JOB_ID % 1000)))

# Only run a few problems for testing
NAMES="${1:-0000_1013_A 0009_1041_A 0012_1060_A}"

set -e
module load cuda/12.3

export DAFNY="$DAFNY"
export Z3_PATH="$Z3"

mkdir -p "$RESULTS_DIR" "$WORK/logs"

echo "=== SMT Quirk Benchmark (llama.cpp test) ==="
echo "Node: $(hostname)"
echo "Model: $MODEL"
echo "Problems: $NAMES"
nvidia-smi --query-gpu=name,memory.total --format=csv
echo ""

# Start llama-server
echo "Starting llama-server..."
$LLAMA_SERVER --model "$MODEL" -ngl 999 -c 8192 -fa on \
    --host 127.0.0.1 --port $PORT &
SERVER_PID=$!

# Wait for server
for i in $(seq 1 60); do
    if curl -s "http://127.0.0.1:$PORT/health" | grep -q '"status":"ok"' 2>/dev/null; then
        echo "Server ready after $((i * 5))s"
        break
    fi
    sleep 5
done

if ! curl -s "http://127.0.0.1:$PORT/health" | grep -q '"status":"ok"' 2>/dev/null; then
    echo "ERROR: Server not ready"
    kill $SERVER_PID 2>/dev/null
    exit 1
fi

# Run benchmark (sequential — llama.cpp handles 1 request at a time)
echo "Running benchmark..."
python3 "$BENCHMARK_DIR/run_benchmark.py" \
    --inputs-dir "$INPUTS_DIR" \
    --output-dir "$RESULTS_DIR" \
    --backend llama \
    --url "http://127.0.0.1:$PORT" \
    --workers 1 \
    --timeout 500 \
    --names $NAMES

echo ""
echo "Results: $RESULTS_DIR"
cat "$RESULTS_DIR/summary.json"

kill $SERVER_PID 2>/dev/null || true
