#!/bin/bash
#SBATCH --job-name=build-z3
#SBATCH --output=build-z3-%j.log
#SBATCH --error=build-z3-%j.err
#SBATCH --partition=boost_usr_prod
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --time=02:00:00
#SBATCH --account=EUHPC_D29_022

module load python/3.11.7
module load gcc/12.2.0
module load cmake

WORK_DIR="/leonardo_work/EUHPC_D29_022/mchiesa0"
Z3_DIR="$WORK_DIR/software/z3"

echo "=== Building Z3 from source ==="
echo "Node: $(hostname)"
echo "GCC: $(gcc --version | head -1)"
echo ""

cd "$WORK_DIR/software"

# Check if z3 source exists
if [ ! -d "z3-src" ]; then
    echo "ERROR: z3 source not found at z3-src"
    echo "Please clone it on login node first:"
    echo "  git clone --depth 1 https://github.com/Z3Prover/z3.git z3-src"
    exit 1
fi

cd z3-src

# Build z3
echo "Configuring z3..."
python3 scripts/mk_make.py --prefix="$Z3_DIR"

echo ""
echo "Building z3 (this will take a while)..."
cd build
make -j8

echo ""
echo "Installing z3..."
make install

echo ""
echo "=== Verifying installation ==="
"$Z3_DIR/bin/z3" --version

echo ""
echo "=== Build complete ==="
echo "Z3 installed to: $Z3_DIR"
