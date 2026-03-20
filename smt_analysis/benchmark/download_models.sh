#!/bin/bash
#SBATCH --job-name=download
#SBATCH --output=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/download_%j.out
#SBATCH --error=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/download_%j.err
#SBATCH --time=04:00:00
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=32G
#SBATCH --partition=lrd_all_serial
#SBATCH --qos=normal
#SBATCH --account=EUHPC_D29_022

# Download models for the benchmark.
# Run on login/serial partition (no GPU needed, just network + disk).
#
# Usage:
#   sbatch download_models.sh                    # download all missing
#   sbatch download_models.sh kimi-dev-72b       # download specific model

set -e

WORK="/leonardo_work/EUHPC_D29_022/mchiesa0"
MODELS_DIR="$WORK/models"

module load python/3.11.7

echo "=== Model Download ==="
echo "Target: $MODELS_DIR"
echo "Free space: $(df -h $WORK | tail -1 | awk '{print $4}')"
echo ""

download_model() {
    local name=$1
    local repo=$2
    local dest=$3

    if [ -d "$MODELS_DIR/$dest" ] && [ -f "$MODELS_DIR/$dest/config.json" ]; then
        echo "SKIP $name: already exists at $MODELS_DIR/$dest"
        return
    fi

    echo "Downloading $name from $repo..."
    python3 -c "
from huggingface_hub import snapshot_download
snapshot_download(
    repo_id='$repo',
    local_dir='$MODELS_DIR/$dest',
    local_dir_use_symlinks=False,
)
print('Done: $name')
"
    echo ""
}

TARGET="${1:-all}"

if [ "$TARGET" = "all" ] || [ "$TARGET" = "kimi-dev-72b" ]; then
    download_model "Kimi-Dev-72B" "moonshotai/Kimi-Dev-72B" "Kimi-Dev-72B"
fi

if [ "$TARGET" = "all" ] || [ "$TARGET" = "qwen3-coder-30b-a3b" ]; then
    download_model "Qwen3-Coder-30B-A3B-Instruct-FP8" "Qwen/Qwen3-Coder-30B-A3B-Instruct-FP8" "Qwen3-Coder-30B-A3B-Instruct-FP8"
fi

echo ""
echo "=== Download complete ==="
ls -la $MODELS_DIR/
df -h $WORK | tail -1
