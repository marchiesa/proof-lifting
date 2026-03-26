#!/bin/bash
#SBATCH --job-name=test-dafny
#SBATCH --output=test-dafny-%j.log
#SBATCH --error=test-dafny-%j.err
#SBATCH --partition=boost_usr_prod
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --time=00:10:00
#SBATCH --account=EUHPC_D29_022

WORK_DIR="/leonardo_work/EUHPC_D29_022/mchiesa0"
DAFNY="$WORK_DIR/software/dafny/dafny"
Z3="$WORK_DIR/software/z3/bin/z3"

echo "=== Test Dafny Verification ==="
echo "Node: $(hostname)"
echo "Dafny: $DAFNY"
echo "Z3: $Z3"
echo ""

# Test z3
echo "Testing z3..."
$Z3 --version

# Create a simple verified program
cat > /tmp/simple.dfy << 'EOF'
method Add(x: int, y: int) returns (r: int)
  ensures r == x + y
{
  r := x + y;
}
EOF

echo ""
echo "=== Simple program (should verify) ==="
cat /tmp/simple.dfy
echo ""
echo "Running Dafny..."
$DAFNY verify --solver-path "$Z3" /tmp/simple.dfy

echo ""
echo "=== Test complete ==="
