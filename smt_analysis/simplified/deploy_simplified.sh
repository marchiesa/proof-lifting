#!/bin/bash
# Deploy simplified benchmark to Leonardo.
#
# Usage (from project root):
#   bash smt_analysis/simplified/deploy_simplified.sh
#
# Then on Leonardo:
#   sbatch --gres=gpu:4 $WORK/simplified/launch_simplified.sh --model gpt-oss-20b

set -e

REMOTE="login.leonardo.cineca.it"
REMOTE_DIR="/leonardo_work/EUHPC_D29_022/mchiesa0/simplified"

echo "Uploading simplified benchmark to Leonardo..."
ssh $REMOTE "mkdir -p $REMOTE_DIR/examples $REMOTE_DIR/results"

# Upload examples
rsync -avz --progress smt_analysis/simplified/examples/ "$REMOTE:$REMOTE_DIR/examples/"

# Upload scripts
scp smt_analysis/simplified/benchmark_simplified.py "$REMOTE:$REMOTE_DIR/"
scp smt_analysis/simplified/launch_simplified.sh "$REMOTE:$REMOTE_DIR/"

echo ""
echo "Deployed to $REMOTE:$REMOTE_DIR"
echo ""
echo "Run on Leonardo:"
echo "  sbatch --gres=gpu:4 $REMOTE_DIR/launch_simplified.sh --model gpt-oss-20b"
echo "  sbatch --gres=gpu:4 $REMOTE_DIR/launch_simplified.sh --model qwen3-coder-next"
