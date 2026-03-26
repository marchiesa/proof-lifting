#!/bin/bash
#SBATCH --job-name=verus-bench
#SBATCH --output=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/verus_bench_%j.out
#SBATCH --error=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/verus_bench_%j.err
#SBATCH --time=04:00:00
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=128G
#SBATCH --partition=boost_usr_prod
#SBATCH --qos=normal
#SBATCH --account=EUHPC_D29_022

# Verus benchmark launcher for Leonardo.
#
# Usage:
#   sbatch --gres=gpu:4 launch.sh --model gpt-oss-20b --mode full
#   sbatch --gres=gpu:4 launch.sh --model kimi-dev-72b --mode full --timeout 5000 --tag 5000s
#   sbatch --gres=gpu:4 launch.sh --model gpt-oss-20b --mode full --run-id 1

set -e

MODEL=""
MODE="full"
NAMES=""
WORKERS=8
TIMEOUT=500
TAG=""
RUN_ID=""

while [[ $# -gt 0 ]]; do
    case $1 in
        --model) MODEL="$2"; shift 2 ;;
        --mode) MODE="$2"; shift 2 ;;
        --names) NAMES="$2"; shift 2 ;;
        --workers) WORKERS="$2"; shift 2 ;;
        --timeout) TIMEOUT="$2"; shift 2 ;;
        --tag) TAG="$2"; shift 2 ;;
        --run-id) RUN_ID="$2"; shift 2 ;;
        *) echo "Unknown arg: $1"; exit 1 ;;
    esac
done

if [ -z "$MODEL" ]; then
    echo "ERROR: --model required"
    exit 1
fi

# --- Paths ---
WORK="/leonardo_work/EUHPC_D29_022/mchiesa0"
BENCHMARK_DIR="$WORK/benchmark_verus"
INPUTS_DIR="$BENCHMARK_DIR/inputs"
MODELS_DIR="$WORK/models"
RESULTS_SUFFIX="${MODE}_${MODEL}"
[ -n "$TAG" ] && RESULTS_SUFFIX="${RESULTS_SUFFIX}_${TAG}"
[ -n "$RUN_ID" ] && RESULTS_SUFFIX="${RESULTS_SUFFIX}_run${RUN_ID}"
RESULTS_DIR="$BENCHMARK_DIR/results/${RESULTS_SUFFIX}"
PORT=$((8000 + (SLURM_JOB_ID % 1000)))

module load python/3.11.7 cuda/12.3
source "$WORK/software/sglang_env/bin/activate"

# Verus via Singularity
VERUS_DIR="$WORK/software/verus"
export VERUS_BIN="$VERUS_DIR/verus-x86-linux/verus"
export VERUS_SIF="$VERUS_DIR/ubuntu_22.04.sif"
export CARGO_BIN="$WORK/software/cargo/bin"
export RUSTUP_HOME="$WORK/software/rustup"
export CARGO_HOME="$WORK/software/cargo"

mkdir -p "$RESULTS_DIR" "$WORK/logs"

# Test verus works
echo "Testing Verus..."
singularity exec --bind /leonardo_work:/leonardo_work \
  --env PATH=$CARGO_BIN:$PATH \
  --env RUSTUP_HOME=$RUSTUP_HOME \
  --env CARGO_HOME=$CARGO_HOME \
  $VERUS_SIF $VERUS_BIN --version
echo ""

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

echo "=== Verus Benchmark ==="
echo "Model: $MODEL ($MODEL_PATH)"
echo "Mode: $MODE"
echo "TP: $TP, Workers: $WORKERS, Timeout: ${TIMEOUT}s"
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

# --- Run benchmark ---
if [ "$MODE" = "placeholder" ]; then
    SCRIPT="$BENCHMARK_DIR/run_placeholder_verus.py"
else
    SCRIPT="$BENCHMARK_DIR/run_benchmark_verus.py"
fi

CMD="python3 $SCRIPT \
    --inputs-dir $INPUTS_DIR \
    --output-dir $RESULTS_DIR \
    --backend sglang \
    --url http://127.0.0.1:$PORT \
    --workers $WORKERS \
    --timeout $TIMEOUT"

[ -n "$NAMES" ] && CMD="$CMD --names $NAMES"

export BENCHMARK_MODEL="$MODEL"
export BENCHMARK_CHAT_API="$CHAT_API"
export BENCHMARK_CHAT_TEMPLATE="$CHAT_TEMPLATE"
export BENCHMARK_STOP_TOKENS="$STOP_TOKENS"

echo "Running: $CMD"
echo ""
eval $CMD

echo ""
echo "=== Complete ==="
echo "Results: $RESULTS_DIR"
cat "$RESULTS_DIR/summary.json" 2>/dev/null || true

kill $SERVER_PID 2>/dev/null || true
