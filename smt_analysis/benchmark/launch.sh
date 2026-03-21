#!/bin/bash
#SBATCH --job-name=bench
#SBATCH --output=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/bench_%j.out
#SBATCH --error=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/bench_%j.err
#SBATCH --time=04:00:00
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
#   sbatch --gres=gpu:4 launch.sh --model kimi-dev-72b --mode full --timeout 5000 --tag 5000s
#   sbatch --gres=gpu:4 launch.sh --model gpt-oss-20b --mode full --names "0000_1013_A 0012_1060_A"
#
# Multi-node (10 nodes, each handles a batch):
#   for i in $(seq 0 9); do
#     sbatch --gres=gpu:4 launch.sh --model kimi-dev-72b --mode full --timeout 5000 \
#       --tag 5000s --batch-id $i --num-batches 10
#   done
#
# Arguments:
#   --model MODEL       Model name (from models.json)
#   --mode MODE         "full" (rewrite) or "placeholder"
#   --names "P1 P2..."  Optional: specific problem names
#   --workers N         Concurrent problems (default: 8)
#   --timeout N         Seconds per problem (default: 500)
#   --tag TAG           Optional: suffix for results dir name
#   --exp-id ID         Experiment ID (shared across all runs in one launch)
#   --run-id N          Run number (for repeated runs with error bars)
#   --batch-id ID       This batch index (0-based, for multi-node)
#   --num-batches N     Total number of batches (for multi-node)

set -e

# --- Parse arguments ---
MODEL=""
MODE="full"
NAMES=""
WORKERS=8
TIMEOUT=500
TAG=""
EXP_ID=""
RUN_ID=""
BATCH_ID=""
NUM_BATCHES=""

while [[ $# -gt 0 ]]; do
    case $1 in
        --model) MODEL="$2"; shift 2 ;;
        --mode) MODE="$2"; shift 2 ;;
        --names) NAMES="$2"; shift 2 ;;
        --workers) WORKERS="$2"; shift 2 ;;
        --timeout) TIMEOUT="$2"; shift 2 ;;
        --tag) TAG="$2"; shift 2 ;;
        --exp-id) EXP_ID="$2"; shift 2 ;;
        --run-id) RUN_ID="$2"; shift 2 ;;
        --batch-id) BATCH_ID="$2"; shift 2 ;;
        --num-batches) NUM_BATCHES="$2"; shift 2 ;;
        *) echo "Unknown arg: $1"; exit 1 ;;
    esac
done

if [ -z "$MODEL" ]; then
    echo "ERROR: --model required"
    exit 1
fi

# --- Paths ---
WORK="/leonardo_work/EUHPC_D29_022/mchiesa0"
BENCHMARK_DIR="$WORK/benchmark"
INPUTS_DIR="$BENCHMARK_DIR/inputs"
MODELS_DIR="$WORK/models"
RESULTS_SUFFIX="${MODE}_${MODEL}"
[ -n "$TAG" ] && RESULTS_SUFFIX="${RESULTS_SUFFIX}_${TAG}"
[ -n "$RUN_ID" ] && RESULTS_SUFFIX="${RESULTS_SUFFIX}_run${RUN_ID}"
[ -n "$BATCH_ID" ] && RESULTS_SUFFIX="${RESULTS_SUFFIX}_batch${BATCH_ID}"
# Use exp-id if provided, otherwise generate timestamp
RESULTS_TS="${EXP_ID:-$(date +%Y%m%d_%H%M%S)}"
RESULTS_DIR="$BENCHMARK_DIR/results_${RESULTS_SUFFIX}_${RESULTS_TS}"
PORT=$((8000 + (SLURM_JOB_ID % 1000)))

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

for i in $(seq 1 360); do
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
    echo "ERROR: Server not ready after 60 min"
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

# If --names specified, use those. Otherwise, if batching, split the problem list.
if [ -n "$NAMES" ]; then
    CMD="$CMD --names $NAMES"
elif [ -n "$BATCH_ID" ] && [ -n "$NUM_BATCHES" ]; then
    # Split manifest problems into batches
    BATCH_NAMES=$(python3 -c "
import json
problems = json.load(open('$INPUTS_DIR/manifest.json'))['problems']
batch_id, num_batches = $BATCH_ID, $NUM_BATCHES
batch = [p for i, p in enumerate(problems) if i % num_batches == batch_id]
print(' '.join(batch))
")
    CMD="$CMD --names $BATCH_NAMES"
    echo "Batch $BATCH_ID/$NUM_BATCHES: $(echo $BATCH_NAMES | wc -w) problems"
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
