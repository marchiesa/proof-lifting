#!/bin/bash
#SBATCH --job-name=tutel-bench
#SBATCH --output=tutel-bench-%j.log
#SBATCH --error=tutel-bench-%j.err
#SBATCH --partition=boost_usr_prod
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --gres=gpu:1
#SBATCH --time=01:00:00
#SBATCH --account=EUHPC_D29_022

module load python/3.11.7
module load cuda/12.3
module load gcc/12.2.0
module load nccl

MODEL_PATH="/leonardo_work/EUHPC_D29_022/mchiesa0/models/gpt-oss-20b-hf"

echo "=== Tutel GPT-OSS-20B Benchmark ==="
echo "Node: $(hostname)"
nvidia-smi
echo ""

python3 << 'EOF'
import torch
import time
from transformers import AutoModelForCausalLM, AutoTokenizer

MODEL_PATH = "/leonardo_work/EUHPC_D29_022/mchiesa0/models/gpt-oss-20b-hf"

print("Loading tokenizer...")
tokenizer = AutoTokenizer.from_pretrained(MODEL_PATH)

print("Loading model...")
start = time.time()
model = AutoModelForCausalLM.from_pretrained(
    MODEL_PATH,
    torch_dtype=torch.bfloat16,
    device_map="cuda",
    trust_remote_code=True,
)
load_time = time.time() - start
print(f"Model loaded in {load_time:.1f}s")

# Warmup
print("\nWarmup...")
prompt = "Hello, how are you?"
inputs = tokenizer(prompt, return_tensors="pt").to("cuda")
with torch.no_grad():
    _ = model.generate(**inputs, max_new_tokens=10, do_sample=False)

# Benchmark
print("\nBenchmarking (512 tokens)...")
prompt = "Write a detailed explanation of how loop invariants work in formal verification. Include examples and explain why they are important for proving program correctness."
inputs = tokenizer(prompt, return_tensors="pt").to("cuda")

torch.cuda.synchronize()
start = time.time()
with torch.no_grad():
    outputs = model.generate(
        **inputs,
        max_new_tokens=512,
        do_sample=True,
        temperature=0.7,
        pad_token_id=tokenizer.eos_token_id,
    )
torch.cuda.synchronize()
elapsed = time.time() - start

tokens_generated = outputs.shape[1] - inputs['input_ids'].shape[1]
throughput = tokens_generated / elapsed

print(f"\n=== Results ===")
print(f"Tokens generated: {tokens_generated}")
print(f"Time elapsed: {elapsed:.2f}s")
print(f"Throughput: {throughput:.2f} tokens/sec")

# Print generated text sample
generated_text = tokenizer.decode(outputs[0], skip_special_tokens=True)
print(f"\nGenerated text (first 500 chars):")
print(generated_text[:500])
EOF

echo ""
echo "=== Benchmark complete ==="
