#!/usr/bin/env python3
"""Benchmark Ollama token generation speed."""
import json
import urllib.request
import sys
import time

def benchmark(model: str, prompt: str, num_tokens: int = 100):
    """Run a benchmark and report speed."""
    url = "http://localhost:11434/api/generate"
    data = json.dumps({
        "model": model,
        "prompt": prompt,
        "stream": False,
        "options": {
            "num_predict": num_tokens
        }
    }).encode("utf-8")

    req = urllib.request.Request(url, data=data, headers={"Content-Type": "application/json"})

    start = time.time()
    with urllib.request.urlopen(req, timeout=300) as response:
        result = json.loads(response.read().decode("utf-8"))
    elapsed = time.time() - start

    eval_count = result.get("eval_count", 0)
    eval_duration = result.get("eval_duration", 0) / 1e9  # ns to s
    prompt_eval_count = result.get("prompt_eval_count", 0)
    prompt_eval_duration = result.get("prompt_eval_duration", 0) / 1e9

    print(f"Prompt tokens: {prompt_eval_count}")
    print(f"Prompt speed: {prompt_eval_count / prompt_eval_duration:.1f} tok/s" if prompt_eval_duration > 0 else "N/A")
    print(f"Generated tokens: {eval_count}")
    print(f"Generation speed: {eval_count / eval_duration:.1f} tok/s" if eval_duration > 0 else "N/A")
    print(f"Total time: {elapsed:.2f}s")

    return eval_count / eval_duration if eval_duration > 0 else 0

if __name__ == "__main__":
    model = sys.argv[1] if len(sys.argv) > 1 else "gpt-oss:20b"

    # Short generation benchmark
    print("=== Short generation (100 tokens) ===")
    speed1 = benchmark(model, "Write a short story about a robot.", 100)

    print("\n=== Medium generation (500 tokens) ===")
    speed2 = benchmark(model, "Explain quantum computing in detail.", 500)

    print(f"\n=== Summary ===")
    print(f"Average generation speed: {(speed1 + speed2) / 2:.1f} tok/s")
