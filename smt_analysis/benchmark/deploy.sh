#!/bin/bash
# Deploy benchmark to Leonardo.
#
# Run from the project root:
#   bash smt_analysis/benchmark/deploy.sh
#
# Then on Leonardo:
#   sbatch $WORK/benchmark/launch_llama.sh    # quick test (1 GPU, 3 problems)
#   sbatch $WORK/benchmark/launch_sglang.sh   # full run (4 GPUs, all problems)

set -e

REMOTE="login.leonardo.cineca.it"
REMOTE_DIR="/leonardo_work/EUHPC_D29_022/mchiesa0/benchmark"

echo "Step 1: Preparing benchmark inputs locally..."
python3 smt_analysis/benchmark/prepare.py
echo ""

echo "Step 2: Uploading to Leonardo..."
ssh $REMOTE "mkdir -p $REMOTE_DIR"

# Upload inputs
rsync -avz --progress smt_analysis/benchmark/inputs/ "$REMOTE:$REMOTE_DIR/inputs/"

# Upload scripts
scp smt_analysis/benchmark/run_benchmark.py "$REMOTE:$REMOTE_DIR/run_benchmark.py"
scp smt_analysis/benchmark/launch_sglang.sh "$REMOTE:$REMOTE_DIR/launch_sglang.sh"
scp smt_analysis/benchmark/launch_llama.sh "$REMOTE:$REMOTE_DIR/launch_llama.sh"

echo ""
echo "Deployed to $REMOTE:$REMOTE_DIR"
echo ""
echo "Next steps on Leonardo:"
echo "  # Quick test (llama.cpp, 1 GPU, 3 problems):"
echo "  sbatch $REMOTE_DIR/launch_llama.sh"
echo ""
echo "  # Full run (SGLang, 4 GPUs, all problems):"
echo "  sbatch $REMOTE_DIR/launch_sglang.sh"
echo ""
echo "  # Monitor:"
echo "  squeue -u mchiesa0"
echo "  tail -f /leonardo_work/EUHPC_D29_022/mchiesa0/logs/quirk-*.out"
