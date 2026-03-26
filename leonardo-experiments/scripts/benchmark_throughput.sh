#!/bin/bash
# Benchmark script for gpt-oss-20b on A100
# Runs entirely on Leonardo - no tunnel needed

set -e

WORK_DIR="/leonardo_work/EUHPC_D29_022/mchiesa0"
SCRIPTS_DIR="$WORK_DIR/scripts"
LOG_DIR="$WORK_DIR/benchmark_logs"
mkdir -p "$LOG_DIR"

TIMESTAMP=$(date +%Y%m%d_%H%M%S)
BENCHMARK_LOG="$LOG_DIR/benchmark_$TIMESTAMP.log"

echo "=== GPT-OSS-20B Throughput Benchmark ===" | tee "$BENCHMARK_LOG"
echo "Started at: $(date)" | tee -a "$BENCHMARK_LOG"
echo "" | tee -a "$BENCHMARK_LOG"

# Submit the server job
echo "Submitting llama-server job..." | tee -a "$BENCHMARK_LOG"
JOB_ID=$(sbatch --parsable "$SCRIPTS_DIR/run_llama_server.sh")
echo "Job ID: $JOB_ID" | tee -a "$BENCHMARK_LOG"

# Wait for job to start running
echo "Waiting for job to start..." | tee -a "$BENCHMARK_LOG"
while true; do
    STATE=$(squeue -j "$JOB_ID" -h -o "%T" 2>/dev/null || echo "COMPLETED")
    if [ "$STATE" = "RUNNING" ]; then
        echo "Job is running!" | tee -a "$BENCHMARK_LOG"
        break
    elif [ "$STATE" = "PENDING" ]; then
        echo "  Job pending... ($(date +%H:%M:%S))"
        sleep 10
    else
        echo "Job ended unexpectedly with state: $STATE" | tee -a "$BENCHMARK_LOG"
        exit 1
    fi
done

# Get the compute node hostname
NODE=$(squeue -j "$JOB_ID" -h -o "%N")
echo "Running on node: $NODE" | tee -a "$BENCHMARK_LOG"

SERVER_URL="http://${NODE}:8080"

# Wait for server to be fully ready using /health endpoint
# Returns {"status":"ok"} when model is loaded, {"status":"loading model"} otherwise
echo "Waiting for model to load (this may take 1-2 minutes)..." | tee -a "$BENCHMARK_LOG"
MAX_WAIT=300
WAITED=0
while [ $WAITED -lt $MAX_WAIT ]; do
    HEALTH=$(curl -s --connect-timeout 5 "${SERVER_URL}/health" 2>/dev/null || echo "FAILED")

    if echo "$HEALTH" | grep -q '"status":"ok"'; then
        echo "Model loaded and ready!" | tee -a "$BENCHMARK_LOG"
        break
    fi

    # Extract status message for logging
    STATUS_MSG=$(echo "$HEALTH" | python3 -c "import sys,json; print(json.load(sys.stdin).get('status','unknown'))" 2>/dev/null || echo "$HEALTH")

    sleep 5
    WAITED=$((WAITED + 5))
    echo "  Waiting... ${WAITED}s (status: ${STATUS_MSG:0:40})"
done

if [ $WAITED -ge $MAX_WAIT ]; then
    echo "ERROR: Model did not load within ${MAX_WAIT}s" | tee -a "$BENCHMARK_LOG"
    echo "Check job log: $SCRIPTS_DIR/llama-server-${JOB_ID}.log"
    scancel "$JOB_ID"
    exit 1
fi

# Run benchmark - generate tokens and measure throughput
echo "" | tee -a "$BENCHMARK_LOG"
echo "=== Running Benchmark ===" | tee -a "$BENCHMARK_LOG"

TEST_PROMPT="Write a detailed explanation of how loop invariants work in formal verification. Include examples and explain why they are important for proving program correctness."

# Warmup request
echo "Warmup request..." | tee -a "$BENCHMARK_LOG"
curl -s -X POST "${SERVER_URL}/v1/completions" \
    -H "Content-Type: application/json" \
    -d '{"prompt": "Hello, how are you?", "n_predict": 50}' >/dev/null

echo "Warmup complete." | tee -a "$BENCHMARK_LOG"

# Benchmark request
echo "Benchmark request (512 tokens)..." | tee -a "$BENCHMARK_LOG"
START_TIME=$(date +%s.%N)

RESPONSE=$(curl -s -X POST "${SERVER_URL}/v1/completions" \
    -H "Content-Type: application/json" \
    -d "{
        \"prompt\": \"$TEST_PROMPT\",
        \"n_predict\": 512,
        \"temperature\": 0.7,
        \"stream\": false
    }")

END_TIME=$(date +%s.%N)

# Parse response
TOKENS_GENERATED=$(echo "$RESPONSE" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('usage',{}).get('completion_tokens', 'N/A'))" 2>/dev/null || echo "N/A")
ELAPSED=$(echo "$END_TIME - $START_TIME" | bc)

echo "" | tee -a "$BENCHMARK_LOG"
echo "=== Results ===" | tee -a "$BENCHMARK_LOG"
echo "Tokens generated: $TOKENS_GENERATED" | tee -a "$BENCHMARK_LOG"
echo "Time elapsed: ${ELAPSED}s" | tee -a "$BENCHMARK_LOG"

if [ "$TOKENS_GENERATED" != "N/A" ] && [ "$TOKENS_GENERATED" -gt 0 ] 2>/dev/null; then
    THROUGHPUT=$(echo "scale=2; $TOKENS_GENERATED / $ELAPSED" | bc)
    echo "Throughput: ${THROUGHPUT} tokens/sec" | tee -a "$BENCHMARK_LOG"
fi

# Also get server-reported timings if available
echo "" | tee -a "$BENCHMARK_LOG"
echo "Server-reported timings:" | tee -a "$BENCHMARK_LOG"
echo "$RESPONSE" | python3 -c "
import sys, json
try:
    d = json.load(sys.stdin)
    timings = d.get('timings', {})
    if timings:
        print(f\"  Prompt eval: {timings.get('prompt_n', 'N/A')} tokens in {timings.get('prompt_ms', 'N/A'):.0f}ms\")
        print(f\"  Generation: {timings.get('predicted_n', 'N/A')} tokens in {timings.get('predicted_ms', 'N/A'):.0f}ms\")
        print(f\"  Generation speed: {timings.get('predicted_per_second', 'N/A'):.2f} tokens/sec\")
    else:
        print('  No timing info in response')
        print('  Raw response (first 500 chars):')
        print(f'  {str(d)[:500]}')
except Exception as e:
    print(f'  Could not parse: {e}')
    print(f'  Raw: {sys.stdin.read()[:500]}')
" 2>&1 | tee -a "$BENCHMARK_LOG"

# Cleanup - cancel the job
echo "" | tee -a "$BENCHMARK_LOG"
echo "Cancelling server job..." | tee -a "$BENCHMARK_LOG"
scancel "$JOB_ID"
echo "Done!" | tee -a "$BENCHMARK_LOG"
echo "" | tee -a "$BENCHMARK_LOG"
echo "Full log saved to: $BENCHMARK_LOG"
