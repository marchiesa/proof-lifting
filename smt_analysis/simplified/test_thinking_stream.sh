#!/bin/bash
#SBATCH --job-name=think-stream
#SBATCH --output=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/think-stream_%j.out
#SBATCH --error=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/think-stream_%j.err
#SBATCH --time=01:00:00
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=128G
#SBATCH --partition=boost_usr_prod
#SBATCH --qos=normal
#SBATCH --account=EUHPC_D29_022

set -e
export PYTHONUNBUFFERED=1

WORK="/leonardo_work/EUHPC_D29_022/mchiesa0"
MODEL_PATH="$WORK/models/Qwen3-Coder-30B-A3B-Instruct"
PORT=8000

module load python/3.11.7 cuda/12.3
source "$WORK/software/sglang_env/bin/activate"

echo "=== Streaming thinking test WITH --reasoning-parser qwen3 ==="

python -m sglang.launch_server \
    --model-path "$MODEL_PATH" \
    --host 127.0.0.1 \
    --port $PORT \
    --tp 4 \
    --mem-fraction-static 0.88 \
    --context-length 16384 \
    --reasoning-parser qwen3 \
    --log-level warning \
    2>&1 &
SERVER_PID=$!

for i in $(seq 1 120); do
    if curl -s "http://127.0.0.1:$PORT/health" > /dev/null 2>&1; then
        echo "Server ready after $((i * 10))s"
        break
    fi
    if ! kill -0 $SERVER_PID 2>/dev/null; then echo "Server died"; exit 1; fi
    sleep 10
done

if ! curl -s "http://127.0.0.1:$PORT/health" > /dev/null 2>&1; then
    echo "Server not ready after 20 min"
    kill $SERVER_PID 2>/dev/null
    exit 1
fi

python3 << 'PYEOF'
import json
import urllib.request
import time
import http.client
import sys

url_base = "http://127.0.0.1:8000"
prompt = """This Dafny program fails verification. Add the missing assert.

method M(a: int, b: int) returns (r: int)
  requires a > 0 && b > 0
  ensures r > 0
{
  r := a * b;
}"""

def test_stream(name, body):
    print(f"\n=== {name} (streaming) ===")
    body["stream"] = True
    t0 = time.time()
    try:
        req = urllib.request.Request(
            f"{url_base}/v1/chat/completions",
            data=json.dumps(body).encode(),
            headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=300) as resp:
            token_count = 0
            all_content = ""
            all_reasoning = ""
            for line in resp:
                line = line.decode().strip()
                if not line.startswith("data: "):
                    continue
                data = line[6:]
                if data == "[DONE]":
                    break
                try:
                    chunk = json.loads(data)
                    delta = chunk["choices"][0].get("delta", {})
                    content = delta.get("content", "") or ""
                    reasoning = delta.get("reasoning_content", "") or ""
                    all_content += content
                    all_reasoning += reasoning
                    token_count += 1
                    # Print first few tokens and periodic updates
                    if token_count <= 5 or token_count % 100 == 0:
                        elapsed = time.time() - t0
                        print(f"  token {token_count} ({elapsed:.1f}s): content={repr(content[:50])} reasoning={repr(reasoning[:50])}")
                        sys.stdout.flush()
                except:
                    pass
        elapsed = time.time() - t0
        print(f"  DONE: {token_count} tokens in {elapsed:.1f}s")
        print(f"  reasoning total: {len(all_reasoning)} chars")
        if all_reasoning:
            print(f"  reasoning[:500]: {all_reasoning[:500]}")
        print(f"  <think> in content: {'<think>' in all_content}")
        print(f"  content total: {len(all_content)} chars")
        print(f"  content[:300]: {all_content[:300]}")
    except Exception as e:
        elapsed = time.time() - t0
        print(f"  ERROR after {elapsed:.1f}s: {e}")
    sys.stdout.flush()

# Test 1: baseline with reasoning-parser server
test_stream("baseline (parser server)", {
    "model": "default",
    "messages": [{"role": "user", "content": prompt}],
    "max_tokens": 4096, "temperature": 0.7,
})

# Test 2: enable_thinking + separate_reasoning with parser server
test_stream("enable_thinking+separate (parser server)", {
    "model": "default",
    "messages": [{"role": "user", "content": prompt}],
    "max_tokens": 4096, "temperature": 0.7,
    "chat_template_kwargs": {"enable_thinking": True},
    "separate_reasoning": True,
})

# Test 3: /think with parser server
test_stream("/think (parser server)", {
    "model": "default",
    "messages": [{"role": "user", "content": prompt + "\n/think"}],
    "max_tokens": 4096, "temperature": 0.7,
})

print("\n=== All streaming tests done ===")
PYEOF

kill $SERVER_PID 2>/dev/null || true
