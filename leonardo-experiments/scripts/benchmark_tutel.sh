#!/bin/bash
#SBATCH --job-name=bench-tutel
#SBATCH --output=bench-tutel-%j.log
#SBATCH --error=bench-tutel-%j.err
#SBATCH --partition=boost_usr_prod
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --gres=gpu:1
#SBATCH --time=01:00:00
#SBATCH --account=EUHPC_D29_022

# Load required modules
module load python/3.11.7
module load cuda/12.3
module load gcc/12.2.0
module load nccl

WORK_DIR="/leonardo_work/EUHPC_D29_022/mchiesa0"

echo "=== Tutel GPT-OSS-20B Benchmark ==="
echo "Node: $(hostname)"
nvidia-smi
echo ""

# Check if GPT-OSS-20B model is available locally
# Tutel uses HuggingFace models directly
MODEL_PATH="$WORK_DIR/models/gpt-oss-20b-hf"

if [ ! -d "$MODEL_PATH" ]; then
    echo "Model not found at $MODEL_PATH"
    echo "Tutel requires the HuggingFace format model, not GGUF."
    echo "Would need to download: huggingface-cli download openai/gpt-oss-20b"
    echo ""
    echo "For now, testing if Tutel can load and run inference..."
fi

# Test Tutel import and basic functionality
python3 << 'EOF'
import torch
import tutel
print(f"PyTorch version: {torch.__version__}")
print(f"CUDA available: {torch.cuda.is_available()}")
if torch.cuda.is_available():
    print(f"GPU: {torch.cuda.get_device_name(0)}")
    print(f"GPU Memory: {torch.cuda.get_device_properties(0).total_memory / 1e9:.1f} GB")

# Test Tutel MoE layer
from tutel import moe as tutel_moe

print("\nTesting Tutel MoE layer...")
# Create a simple MoE layer
moe_layer = tutel_moe.moe_layer(
    gate_type={'type': 'top', 'k': 2},
    experts={'type': 'ffn', 'count_per_node': 8, 'hidden_size_per_expert': 256},
    model_dim=128,
    scan_expert_func=lambda name, param: setattr(param, 'skip_allreduce', True),
).cuda()

# Run a forward pass
x = torch.randn(4, 32, 128).cuda()  # batch=4, seq=32, dim=128
output = moe_layer(x)
print(f"Input shape: {x.shape}")
print(f"Output shape: {output.shape}")
print("Tutel MoE working!")
EOF

echo ""
echo "=== Benchmark complete ==="
