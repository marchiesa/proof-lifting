#!/bin/bash
# Generate dataset problems in a loop until killed.
# Each batch generates 100 problems with 5 workers.
# Results go to dataset/ directory.
#
# Usage: bash generate_loop.sh [start_index] [batch_size] [workers]
# Kill with: kill $(cat /tmp/generate_loop.pid)

echo $$ > /tmp/generate_loop.pid

START=${1:-105}
BATCH=${2:-100}
WORKERS=${3:-10}
BATCH_NUM=0

cd /Users/mchiesa/work/projects/2026-02-dafny-liftings

while true; do
    IDX=$((START + BATCH_NUM * BATCH))
    BATCH_NUM=$((BATCH_NUM + 1))

    echo "=============================================="
    echo "BATCH $BATCH_NUM: problems $IDX to $((IDX + BATCH - 1))"
    echo "Started at $(date)"
    echo "=============================================="

    python3 pipeline.py --start "$IDX" --count "$BATCH" --workers "$WORKERS" --max-rating 1600 2>&1

    echo ""
    echo "Batch $BATCH_NUM finished at $(date)"
    echo "Total problems generated so far: $(ls -d dataset/*/ 2>/dev/null | wc -l)"
    echo ""
done
