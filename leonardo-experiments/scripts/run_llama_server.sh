#!/bin/bash
#SBATCH --job-name=llama-server
#SBATCH --output=llama-server-%j.log
#SBATCH --error=llama-server-%j.err
#SBATCH --partition=boost_usr_prod
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --gres=gpu:1
#SBATCH --time=04:00:00
#SBATCH --account=EUHPC_D29_022

# Load required modules
module load cuda/12.3
module load gcc/12.2.0

# Paths
LLAMA_SERVER="/leonardo_work/EUHPC_D29_022/mchiesa0/software/llama.cpp/build/bin/llama-server"
MODEL="/leonardo_work/EUHPC_D29_022/mchiesa0/models/gpt-oss-20b-mxfp4.gguf"

# Set library path for CUDA
export LD_LIBRARY_PATH=/leonardo/prod/opt/compilers/cuda/12.3/none/lib64:$LD_LIBRARY_PATH

# Get the node hostname for connection info
echo "=== llama-server starting on $(hostname) ==="
echo "Connect via SSH tunnel: ssh -L 8080:$(hostname):8080 mchiesa0@login.leonardo.cineca.it"
echo ""

# Run llama-server with optimizations
$LLAMA_SERVER \
    --model "$MODEL" \
    -ngl 999 \
    -c 8192 \
    -fa on \
    --host 0.0.0.0 \
    --port 8080

# Flags explained:
# -ngl 999        = offload all layers to GPU
# -c 8192         = larger context window (A100 has 64GB, can handle it)
# -fa             = flash attention (major speedup for attention computation)
# --host 0.0.0.0  = listen on all interfaces
