#!/bin/bash
#SBATCH --job-name=bench
#SBATCH --output=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/bench_%j.out
#SBATCH --error=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/bench_%j.err
#SBATCH --time=02:00:00
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=128G
#SBATCH --partition=boost_usr_prod
#SBATCH --qos=normal
#SBATCH --account=EUHPC_D29_022

# Unified benchmark launcher.
#
# Usage:
#   sbatch --gres=gpu:4 launch.sh --model gpt-oss-20b --mode full
#   sbatch --gres=gpu:4 launch.sh --model qwen3-coder-next --mode placeholder
#   sbatch --gres=gpu:1 launch.sh --model goedel-prover-v2-8b --mode full
#   sbatch --gres=gpu:4 launch.sh --model gpt-oss-20b --mode full --names "0000_1013_A 0012_1060_A"
#
# Arguments:
#   --model MODEL       Model name (from models.json)
#   --mode MODE         "full" (rewrite) or "placeholder"
#   --names "P1 P2..."  Optional: specific problem names
#   --workers N         Concurrent problems (default: 8)
#   --timeout N         Seconds per problem (default: 500)

set -e

# --- Parse arguments ---
MODEL=""
MODE="full"
NAMES=""
WORKERS=8
TIMEOUT=500

while [[ $# -gt 0 ]]; do
    case $1 in
        --model) MODEL="$2"; shift 2 ;;
        --mode) MODE="$2"; shift 2 ;;
        --names) NAMES="$2"; shift 2 ;;
        --workers) WORKERS="$2"; shift 2 ;;
        --timeout) TIMEOUT="$2"; shift 2 ;;
        *) echo "Unknown arg: $1"; exit 1 ;;
    esac
done

if [ -z "$MODEL" ]; then
    echo "ERROR: --model required (gpt-oss-20b, qwen3-coder-next, goedel-prover-v2-8b)"
    exit 1
fi

# --- Paths ---
WORK="/leonardo_work/EUHPC_D29_022/mchiesa0"
BENCHMARK_DIR="$WORK/benchmark"
INPUTS_DIR="$BENCHMARK_DIR/inputs"
MODELS_DIR="$WORK/models"
RESULTS_DIR="$BENCHMARK_DIR/results_${MODE}_${MODEL}_$(date +%Y%m%d_%H%M%S)"
PORT=8000

module load python/3.11.7 cuda/12.3
source "$WORK/software/sglang_env/bin/activate"

export DOTNET8="$WORK/software/dotnet8/dotnet"
export DAFNY_DLL="$WORK/software/dafny-modified/Dafny.dll"
export Z3_PATH="$WORK/software/z3/bin/z3"

mkdir -p "$RESULTS_DIR" "$WORK/logs"

# --- Read model config ---
MODEL_CONFIG=$(python3 -c "
import json
models = json.load(open('$BENCHMARK_DIR/models.json'))
m = models.get('$MODEL')
if not m:
    print('ERROR: unknown model $MODEL')
    exit(1)
print(m.get('hf_path', ''))
print(m.get('chat_api', 'true'))
print(m.get('context_length', 16384))
print(m.get('tp', 4))
print('|'.join(m.get('stop_tokens', [])))
ct = m.get('chat_template', '')
print(ct)
")

HF_PATH=$(echo "$MODEL_CONFIG" | sed -n '1p')
CHAT_API=$(echo "$MODEL_CONFIG" | sed -n '2p')
CTX_LEN=$(echo "$MODEL_CONFIG" | sed -n '3p')
TP=$(echo "$MODEL_CONFIG" | sed -n '4p')
STOP_TOKENS=$(echo "$MODEL_CONFIG" | sed -n '5p')
CHAT_TEMPLATE=$(echo "$MODEL_CONFIG" | sed -n '6p')

MODEL_PATH="$MODELS_DIR/$HF_PATH"

echo "=== Benchmark ==="
echo "Model: $MODEL ($MODEL_PATH)"
echo "Mode: $MODE"
echo "TP: $TP, Workers: $WORKERS, Timeout: ${TIMEOUT}s"
echo "Context: $CTX_LEN, Chat API: $CHAT_API"
echo "Node: $(hostname), Job: $SLURM_JOB_ID"
nvidia-smi --query-gpu=name,memory.total --format=csv
echo ""

# --- Start SGLang ---
echo "Starting SGLang server (TP=$TP)..."
python -m sglang.launch_server \
    --model-path "$MODEL_PATH" \
    --host 127.0.0.1 \
    --port $PORT \
    --tp $TP \
    --mem-fraction-static 0.88 \
    --context-length $CTX_LEN \
    --max-running-requests 64 \
    --log-level warning \
    2>&1 &
SERVER_PID=$!

for i in $(seq 1 180); do
    if curl -s "http://127.0.0.1:$PORT/health" > /dev/null 2>&1; then
        echo "Server ready after $((i * 10))s"
        break
    fi
    if ! kill -0 $SERVER_PID 2>/dev/null; then
        echo "ERROR: Server died"
        exit 1
    fi
    sleep 10
done

if ! curl -s "http://127.0.0.1:$PORT/health" > /dev/null 2>&1; then
    echo "ERROR: Server not ready after 30 min"
    kill $SERVER_PID 2>/dev/null
    exit 1
fi

nvidia-smi --query-gpu=memory.used,memory.free --format=csv

# --- Build benchmark command ---
if [ "$MODE" = "placeholder" ]; then
    SCRIPT="$BENCHMARK_DIR/run_placeholder.py"
else
    SCRIPT="$BENCHMARK_DIR/run_benchmark.py"
fi

CMD="python3 $SCRIPT \
    --inputs-dir $INPUTS_DIR \
    --output-dir $RESULTS_DIR \
    --backend sglang \
    --url http://127.0.0.1:$PORT \
    --workers $WORKERS \
    --timeout $TIMEOUT"

if [ -n "$NAMES" ]; then
    CMD="$CMD --names $NAMES"
fi

# Pass model-specific config via env vars
export BENCHMARK_MODEL="$MODEL"
export BENCHMARK_CHAT_API="$CHAT_API"
export BENCHMARK_CHAT_TEMPLATE="$CHAT_TEMPLATE"
export BENCHMARK_STOP_TOKENS="$STOP_TOKENS"

echo ""
echo "Running: $CMD"
echo ""
eval $CMD

echo ""
echo "=== Complete ==="
echo "Results: $RESULTS_DIR"
cat "$RESULTS_DIR/summary.json" 2>/dev/null || true

kill $SERVER_PID 2>/dev/null || true
