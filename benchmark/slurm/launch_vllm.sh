#!/usr/bin/env bash
#
# Launch a vLLM OpenAI-compatible server on a single GPU.
#
# Usage:
#   ./launch_vllm.sh <model_name> <port> <gpu_id>
#
# Example:
#   ./launch_vllm.sh meta-llama/Llama-3.1-70B-Instruct 8000 0
#
# The script:
#   1. Pins to the given GPU via CUDA_VISIBLE_DEVICES
#   2. Starts vLLM's OpenAI-compatible server in the background
#   3. Waits until the /health endpoint responds (up to 10 min)
#   4. Prints the endpoint URL to stdout
#
# Prerequisites:
#   pip install vllm
#
set -euo pipefail

if [[ $# -lt 3 ]]; then
    echo "Usage: $0 <model_name> <port> <gpu_id>" >&2
    exit 1
fi

MODEL="$1"
PORT="$2"
GPU_ID="$3"

# Optional: tensor-parallel size (defaults to 1).
TP_SIZE="${4:-1}"

export CUDA_VISIBLE_DEVICES="$GPU_ID"

LOG_FILE="/tmp/vllm_gpu${GPU_ID}_port${PORT}.log"

echo "[launch_vllm] Starting vLLM server"
echo "  Model:  $MODEL"
echo "  Port:   $PORT"
echo "  GPU:    $GPU_ID"
echo "  TP:     $TP_SIZE"
echo "  Log:    $LOG_FILE"

# Start the server in the background.
python -m vllm.entrypoints.openai.api_server \
    --model "$MODEL" \
    --port "$PORT" \
    --tensor-parallel-size "$TP_SIZE" \
    --trust-remote-code \
    > "$LOG_FILE" 2>&1 &

VLLM_PID=$!
echo "[launch_vllm] vLLM PID: $VLLM_PID"

# Health-check loop: wait up to 600 seconds (10 min) for the server to become
# ready.  Large models on A100 may take several minutes to load.
MAX_WAIT=600
ELAPSED=0
INTERVAL=5

while (( ELAPSED < MAX_WAIT )); do
    if ! kill -0 "$VLLM_PID" 2>/dev/null; then
        echo "[launch_vllm] ERROR: vLLM process exited prematurely. See $LOG_FILE" >&2
        exit 1
    fi
    if curl -sf "http://localhost:${PORT}/health" > /dev/null 2>&1; then
        echo "[launch_vllm] Server ready after ${ELAPSED}s"
        echo "http://localhost:${PORT}/v1"
        exit 0
    fi
    sleep "$INTERVAL"
    ELAPSED=$(( ELAPSED + INTERVAL ))
done

echo "[launch_vllm] ERROR: Server did not become ready within ${MAX_WAIT}s" >&2
kill "$VLLM_PID" 2>/dev/null || true
exit 1
