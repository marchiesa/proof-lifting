#!/bin/bash
#SBATCH --job-name=dafny-llm
#SBATCH --output=dafny-llm-%j.log
#SBATCH --error=dafny-llm-%j.err
#SBATCH --partition=boost_usr_prod
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --gres=gpu:1
#SBATCH --time=01:00:00
#SBATCH --account=EUHPC_D29_022

module load cuda/12.3
module load gcc/12.2.0
module load python/3.11.7

WORK_DIR="/leonardo_work/EUHPC_D29_022/mchiesa0"
LLAMA_SERVER="$WORK_DIR/software/llama.cpp/build/bin/llama-server"
MODEL="$WORK_DIR/models/gpt-oss-20b-mxfp4.gguf"
DAFNY="$WORK_DIR/software/dafny/dafny"
Z3="$WORK_DIR/software/z3/bin/z3"
PROVER_SCRIPT="$WORK_DIR/scripts/dafny_prover_llama.py"

# Input file (default or from argument)
DAFNY_FILE="${1:-$WORK_DIR/benchmarks/01_max_element.dfy}"
# Use unique port based on job ID to avoid conflicts when multiple jobs on same node
PORT=$((8000 + (SLURM_JOB_ID % 1000)))

echo "=== Dafny LLM Experiment ==="
echo "Node: $(hostname)"
echo "Input: $DAFNY_FILE"
nvidia-smi
echo ""

# Start llama-server in background
echo "Starting llama-server..."
$LLAMA_SERVER --model "$MODEL" -ngl 999 -c 8192 -fa on --host 127.0.0.1 --port $PORT &
SERVER_PID=$!

# Wait for server to be ready
echo "Waiting for model to load..."
MAX_WAIT=300
WAITED=0
while [ $WAITED -lt $MAX_WAIT ]; do
    HEALTH=$(curl -s http://127.0.0.1:$PORT/health 2>/dev/null)
    if echo "$HEALTH" | grep -q '"status":"ok"'; then
        echo "Server ready after ${WAITED}s"
        break
    fi
    sleep 5
    WAITED=$((WAITED + 5))
done

if [ $WAITED -ge $MAX_WAIT ]; then
    echo "ERROR: Server failed to start within ${MAX_WAIT}s"
    kill $SERVER_PID 2>/dev/null
    exit 1
fi

# Run the prover
echo ""
echo "Running dafny_prover_llama.py..."
# Generate unique output filename based on input and job ID
INPUT_BASENAME=$(basename "$DAFNY_FILE" .dfy)
OUTPUT_FILE="${INPUT_BASENAME}_verified_${SLURM_JOB_ID}.dfy"

python3 "$PROVER_SCRIPT" "$DAFNY_FILE" \
    --url "http://127.0.0.1:$PORT" \
    --dafny "$DAFNY" \
    --z3 "$Z3" \
    --max-attempts 5 \
    --output "$OUTPUT_FILE" \
    --log "prover_${SLURM_JOB_ID}.log"

EXIT_CODE=$?

# Cleanup
kill $SERVER_PID 2>/dev/null

echo ""
echo "=== Experiment complete (exit code: $EXIT_CODE) ==="
exit $EXIT_CODE
