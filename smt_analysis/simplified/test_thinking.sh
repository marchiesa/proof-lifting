#!/bin/bash
#SBATCH --job-name=think-test
#SBATCH --output=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/think-test_%j.out
#SBATCH --error=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/think-test_%j.err
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

echo "=== Thinking mode test ==="

# Start server WITHOUT reasoning parser first
python -m sglang.launch_server \
    --model-path "$MODEL_PATH" \
    --host 127.0.0.1 \
    --port $PORT \
    --tp 4 \
    --mem-fraction-static 0.88 \
    --context-length 16384 \
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

# Write the test script
python3 << 'PYEOF'
import json
import urllib.request

url = "http://127.0.0.1:8000/v1/chat/completions"
prompt = """This Dafny program fails verification. Add the missing assert.

method M(a: int, b: int) returns (r: int)
  requires a > 0 && b > 0
  ensures r > 0
{
  r := a * b;
}"""

def test(name, body):
    print(f"\n=== {name} ===")
    try:
        req = urllib.request.Request(url, data=json.dumps(body).encode(),
                                     headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=120) as resp:
            r = json.loads(resp.read())
        msg = r["choices"][0]["message"]
        content = msg.get("content", "") or ""
        reasoning = msg.get("reasoning_content", "") or ""
        tokens = r.get("usage", {}).get("completion_tokens", 0)
        print(f"  tokens: {tokens}")
        print(f"  reasoning_content len: {len(reasoning)}")
        if reasoning:
            print(f"  reasoning[:300]: {reasoning[:300]}")
        has_think = "<think>" in content
        print(f"  <think> in content: {has_think}")
        print(f"  content len: {len(content)}")
        print(f"  content[:400]: {content[:400]}")
    except Exception as e:
        print(f"  ERROR: {e}")

# Test 1: baseline
test("baseline", {
    "model": "default",
    "messages": [{"role": "user", "content": prompt}],
    "max_tokens": 2048, "temperature": 0.7,
})

# Test 2: enable_thinking=true via chat_template_kwargs
test("enable_thinking=true", {
    "model": "default",
    "messages": [{"role": "user", "content": prompt}],
    "max_tokens": 2048, "temperature": 0.7,
    "chat_template_kwargs": {"enable_thinking": True},
})

# Test 3: /think soft switch in prompt
test("/think in prompt", {
    "model": "default",
    "messages": [{"role": "user", "content": prompt + "\n/think"}],
    "max_tokens": 2048, "temperature": 0.7,
})

# Test 4: enable_thinking + separate_reasoning
test("enable_thinking + separate_reasoning", {
    "model": "default",
    "messages": [{"role": "user", "content": prompt}],
    "max_tokens": 2048, "temperature": 0.7,
    "chat_template_kwargs": {"enable_thinking": True},
    "separate_reasoning": True,
})

# Test 5: /think + enable_thinking + separate_reasoning
test("/think + enable_thinking + separate_reasoning", {
    "model": "default",
    "messages": [{"role": "user", "content": prompt + "\n/think"}],
    "max_tokens": 2048, "temperature": 0.7,
    "chat_template_kwargs": {"enable_thinking": True},
    "separate_reasoning": True,
})

print("\n=== All tests done ===")
PYEOF

kill $SERVER_PID 2>/dev/null || true
