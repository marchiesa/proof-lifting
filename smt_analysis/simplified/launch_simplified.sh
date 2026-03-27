#!/bin/bash
#SBATCH --job-name=simp-bench
#SBATCH --output=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/simp-bench_%j.out
#SBATCH --error=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/simp-bench_%j.err
#SBATCH --time=04:00:00
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=128G
#SBATCH --partition=boost_usr_prod
#SBATCH --qos=normal
#SBATCH --account=EUHPC_D29_022

# End-to-end simplified benchmark.
#
# Usage:
#   sbatch --gres=gpu:4 launch_simplified.sh --model gpt-oss-20b
#   sbatch --gres=gpu:4 launch_simplified.sh --model qwen3-coder-next
#   sbatch --gres=gpu:1 launch_simplified.sh --model gpt-oss-20b --tp 1

set -e

# --- Parse arguments ---
MODEL=""
TP=""
TIMEOUT=300
TEMPERATURE=0.7
RUN_ID=""
LANG="dafny"

while [[ $# -gt 0 ]]; do
    case $1 in
        --model) MODEL="$2"; shift 2 ;;
        --tp) TP="$2"; shift 2 ;;
        --timeout) TIMEOUT="$2"; shift 2 ;;
        --temperature) TEMPERATURE="$2"; shift 2 ;;
        --run-id) RUN_ID="$2"; shift 2 ;;
        --lang) LANG="$2"; shift 2 ;;
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
SIMPLIFIED_DIR="$WORK/simplified"
MODELS_DIR="$WORK/models"
PORT=8000

module load python/3.11.7 cuda/12.3
source "$WORK/software/sglang_env/bin/activate"

export DOTNET8="$WORK/software/dotnet8/dotnet"
export DAFNY_DLL="$WORK/software/dafny-modified/Dafny.dll"
export Z3_PATH="$WORK/software/z3/bin/z3"
export VERUS_BIN="$WORK/software/verus/verus-x86-linux/verus"

mkdir -p "$SIMPLIFIED_DIR/results" "$WORK/logs"

# --- Read model config ---
MODEL_CONFIG=$(python3 -c "
import json, sys
models = json.load(open('$BENCHMARK_DIR/models.json'))
m = models.get('$MODEL')
if not m:
    print('ERROR', file=sys.stderr)
    sys.exit(1)
print(m.get('hf_path', ''))
print(m.get('chat_api', 'true'))
print(m.get('context_length', 16384))
print(m.get('tp', 4))
print('|'.join(m.get('stop_tokens', [])))
ct = m.get('chat_template', '')
print(ct)
print(m.get('reasoning_parser', ''))
")

HF_PATH=$(echo "$MODEL_CONFIG" | sed -n '1p')
CHAT_API=$(echo "$MODEL_CONFIG" | sed -n '2p')
CTX_LEN=$(echo "$MODEL_CONFIG" | sed -n '3p')
DEFAULT_TP=$(echo "$MODEL_CONFIG" | sed -n '4p')
STOP_TOKENS=$(echo "$MODEL_CONFIG" | sed -n '5p')
CHAT_TEMPLATE=$(echo "$MODEL_CONFIG" | sed -n '6p')
REASONING_PARSER=$(echo "$MODEL_CONFIG" | sed -n '7p')

TP=${TP:-$DEFAULT_TP}
MODEL_PATH="$MODELS_DIR/$HF_PATH"

export PYTHONUNBUFFERED=1
export BENCHMARK_MODEL="$MODEL"
export BENCHMARK_CHAT_API="$CHAT_API"
export BENCHMARK_CHAT_TEMPLATE="$CHAT_TEMPLATE"
export BENCHMARK_STOP_TOKENS="$STOP_TOKENS"
export BENCHMARK_REASONING_PARSER="$REASONING_PARSER"

echo "=== Simplified Benchmark ==="
echo "Model: $MODEL ($MODEL_PATH)"
echo "TP: $TP, Timeout: ${TIMEOUT}s"
echo "Node: $(hostname), Job: $SLURM_JOB_ID"
nvidia-smi --query-gpu=name,memory.total --format=csv
echo ""

# --- Start SGLang ---
echo "Starting SGLang server (TP=$TP)..."
SGLANG_ARGS="--model-path $MODEL_PATH --host 127.0.0.1 --port $PORT --tp $TP --mem-fraction-static 0.88 --context-length $CTX_LEN --log-level warning"
[ -n "$REASONING_PARSER" ] && SGLANG_ARGS="$SGLANG_ARGS --reasoning-parser $REASONING_PARSER"
echo "SGLang args: $SGLANG_ARGS"
python -m sglang.launch_server $SGLANG_ARGS 2>&1 &
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
    echo "ERROR: Server not ready"
    kill $SERVER_PID 2>/dev/null
    exit 1
fi

nvidia-smi --query-gpu=memory.used,memory.free --format=csv

# --- Run benchmark ---
echo ""
echo "Running simplified benchmark..."
BENCH_ARGS="--url http://127.0.0.1:$PORT --backend sglang --timeout $TIMEOUT --temperature $TEMPERATURE --lang $LANG"
[ -n "$RUN_ID" ] && BENCH_ARGS="$BENCH_ARGS --run-id $RUN_ID"
[ -n "$REASONING_PARSER" ] && BENCH_ARGS="$BENCH_ARGS --model-suffix thinking"

# Build output dir name
LANG_PREFIX=""
[ "$LANG" != "dafny" ] && LANG_PREFIX="${LANG}_"
RESULT_NAME="${LANG_PREFIX}${MODEL}${REASONING_PARSER:+-thinking}${RUN_ID:+_run${RUN_ID}}"
BENCH_ARGS="$BENCH_ARGS --output-dir $SIMPLIFIED_DIR/results/$RESULT_NAME"

echo "Benchmark args: $BENCH_ARGS"
python3 "$SIMPLIFIED_DIR/benchmark_simplified.py" $BENCH_ARGS

echo ""
echo "=== Complete ==="
cat "$SIMPLIFIED_DIR/results/$MODEL/summary.json" 2>/dev/null || true

kill $SERVER_PID 2>/dev/null || true
