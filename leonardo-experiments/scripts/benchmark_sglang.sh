#!/bin/bash
#SBATCH --job-name=sglang_bench
#SBATCH --output=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/sglang_bench_%j.out
#SBATCH --error=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/sglang_bench_%j.err
#SBATCH --time=00:30:00
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=64G
#SBATCH --partition=boost_usr_prod
#SBATCH --qos=normal
#SBATCH --account=EUHPC_D29_022
#SBATCH --gres=gpu:1

set -e

# Paths
MODEL_PATH="/leonardo_work/EUHPC_D29_022/mchiesa0/models/gpt-oss-20b-hf"
SGLANG_ENV="/leonardo_work/EUHPC_D29_022/mchiesa0/software/sglang_env"
PORT=8000

echo "=== SGLang Benchmark Script ==="
echo "Job ID: $SLURM_JOB_ID"
echo "Node: $(hostname)"
echo "Date: $(date)"
echo ""

# Load modules
module load python/3.10.8--gcc--11.3.0
module load cuda/12.3

# Activate SGLang environment
source "$SGLANG_ENV/bin/activate"

# Check GPU
echo "=== GPU Info ==="
nvidia-smi --query-gpu=name,memory.total,memory.free --format=csv
echo ""

echo "Using SGLang version: $(pip show sglang | grep Version)"
echo ""

# Start SGLang server in background
echo "=== Starting SGLang Server ==="
python -m sglang.launch_server \
    --model-path "$MODEL_PATH" \
    --host 127.0.0.1 \
    --port $PORT \
    --mem-fraction-static 0.85 \
    --context-length 4096 \
    2>&1 | tee sglang_server.log &

SERVER_PID=$!
echo "Server PID: $SERVER_PID"

# Wait for server to be ready
echo "Waiting for server to start..."
MAX_WAIT=600
WAITED=0
while ! curl -s http://127.0.0.1:$PORT/health > /dev/null 2>&1; do
    sleep 5
    WAITED=$((WAITED + 5))
    if [ $WAITED -ge $MAX_WAIT ]; then
        echo "ERROR: Server failed to start within $MAX_WAIT seconds"
        echo "=== Server Log ==="
        cat sglang_server.log
        kill $SERVER_PID 2>/dev/null || true
        exit 1
    fi
    echo "  Waiting... ($WAITED s)"
done
echo "Server is ready!"
echo ""

# Check memory after model load
echo "=== GPU Memory After Model Load ==="
nvidia-smi --query-gpu=memory.used,memory.free,memory.total --format=csv
echo ""

# Create the benchmark Python script
cat > /tmp/benchmark_sglang.py << 'PYTHON_SCRIPT'
#!/usr/bin/env python3
"""Benchmark SGLang with different batch sizes."""

import asyncio
import aiohttp
import time
from dataclasses import dataclass
from typing import List

SERVER_URL = "http://127.0.0.1:8000"

# Test prompt - a Dafny verification task
TEST_PROMPT = """You are a Dafny verification expert. Add loop invariants to make this code verify:

```dafny
method MaxElement(s: seq<int>) returns (max: int)
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> max >= s[i]
{
  max := s[0];
  var idx := 1;
  while idx < |s|
  {
    if s[idx] > max { max := s[idx]; }
    idx := idx + 1;
  }
}
```

Output the complete code with invariants:
<DAFNY_CODE>
"""

@dataclass
class BenchmarkResult:
    batch_size: int
    total_time: float
    total_tokens: int
    tokens_per_second: float
    avg_latency: float

async def send_request(session: aiohttp.ClientSession, prompt: str, max_tokens: int = 512) -> dict:
    """Send a single request and return timing info."""
    payload = {
        "text": prompt,
        "sampling_params": {
            "max_new_tokens": max_tokens,
            "temperature": 0.7,
        }
    }

    start = time.perf_counter()
    async with session.post(f"{SERVER_URL}/generate", json=payload) as resp:
        result = await resp.json()
    end = time.perf_counter()

    if "error" in result:
        print(f"Error: {result['error']}")
        return {"tokens": 0, "time": end - start}

    # Extract token count from response
    completion_tokens = result.get("meta_info", {}).get("completion_tokens", 0)
    if completion_tokens == 0:
        # Estimate from text length
        text = result.get("text", "")
        completion_tokens = len(text) // 4  # rough estimate

    return {
        "tokens": completion_tokens,
        "time": end - start,
        "text": result.get("text", "")[:100]
    }

async def benchmark_batch(batch_size: int) -> BenchmarkResult:
    """Run benchmark with specified batch size."""
    print(f"\n{'='*50}")
    print(f"Benchmarking batch size: {batch_size}")
    print(f"{'='*50}")

    async with aiohttp.ClientSession() as session:
        # Create batch of requests
        tasks = [send_request(session, TEST_PROMPT) for _ in range(batch_size)]

        # Run all requests concurrently
        start = time.perf_counter()
        results = await asyncio.gather(*tasks)
        total_time = time.perf_counter() - start

        # Calculate stats
        total_tokens = sum(r["tokens"] for r in results)
        avg_latency = sum(r["time"] for r in results) / len(results)
        tokens_per_second = total_tokens / total_time if total_time > 0 else 0

        print(f"Total time: {total_time:.2f}s")
        print(f"Total tokens generated: {total_tokens}")
        print(f"Throughput: {tokens_per_second:.1f} tokens/s")
        print(f"Average latency per request: {avg_latency:.2f}s")
        print(f"Sample response: {results[0]['text'][:80]}...")

        return BenchmarkResult(
            batch_size=batch_size,
            total_time=total_time,
            total_tokens=total_tokens,
            tokens_per_second=tokens_per_second,
            avg_latency=avg_latency
        )

async def main():
    print("="*60)
    print("SGLang Throughput Benchmark")
    print("="*60)

    # Warm up
    print("\nWarm-up run...")
    async with aiohttp.ClientSession() as session:
        await send_request(session, "Hello", max_tokens=10)
    print("Warm-up complete.\n")

    # Run benchmarks
    batch_sizes = [1, 2, 4, 8]
    results: List[BenchmarkResult] = []

    for batch_size in batch_sizes:
        result = await benchmark_batch(batch_size)
        results.append(result)
        # Small pause between tests
        await asyncio.sleep(2)

    # Summary
    print("\n" + "="*60)
    print("BENCHMARK SUMMARY")
    print("="*60)
    print(f"{'Batch':<8} {'Time(s)':<10} {'Tokens':<10} {'Tok/s':<12} {'Latency(s)':<12}")
    print("-"*60)
    for r in results:
        print(f"{r.batch_size:<8} {r.total_time:<10.2f} {r.total_tokens:<10} {r.tokens_per_second:<12.1f} {r.avg_latency:<12.2f}")

    # Scaling analysis
    if len(results) >= 2 and results[0].tokens_per_second > 0:
        print("\nScaling efficiency (vs batch=1):")
        baseline = results[0].tokens_per_second
        for r in results[1:]:
            efficiency = (r.tokens_per_second / (baseline * r.batch_size)) * 100
            print(f"  Batch {r.batch_size}: {efficiency:.1f}% efficiency ({r.tokens_per_second:.1f} vs ideal {baseline * r.batch_size:.1f} tok/s)")

if __name__ == "__main__":
    asyncio.run(main())
PYTHON_SCRIPT

# Run benchmark
echo "=== Running Benchmark ==="
python /tmp/benchmark_sglang.py

# Final memory check
echo ""
echo "=== Final GPU Memory ==="
nvidia-smi --query-gpu=memory.used,memory.free,memory.total --format=csv

# Cleanup
echo ""
echo "=== Cleanup ==="
kill $SERVER_PID 2>/dev/null || true
wait $SERVER_PID 2>/dev/null || true
echo "Server stopped."
echo ""
echo "Benchmark complete!"
