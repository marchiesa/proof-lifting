#!/bin/bash
#SBATCH --job-name=build-tutel
#SBATCH --output=build-tutel-%j.log
#SBATCH --error=build-tutel-%j.err
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

# Set CUDA arch for A100
export TORCH_CUDA_ARCH_LIST='8.0'

TUTEL_SRC="/leonardo_work/EUHPC_D29_022/mchiesa0/software/tutel-src"

echo "=== Building Tutel on compute node ==="
echo "Node: $(hostname)"
echo "CUDA: $(nvcc --version | grep release)"
nvidia-smi
echo ""

# Clean previous build and install Tutel from local source
echo "Cleaning previous build..."
cd "$TUTEL_SRC"
rm -rf build/ tutel.egg-info/ 2>/dev/null

echo "Installing Tutel from local source..."
python3 -m pip install --user --no-build-isolation . 2>&1

# Verify installation
echo ""
echo "=== Verifying installation ==="
python3 -c "import tutel; print(f'Tutel imported successfully')" 2>&1

echo ""
echo "=== Build complete ==="
