#!/bin/bash
#SBATCH --job-name=qwen3_dafny
#SBATCH --output=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/qwen3_dafny_%j.out
#SBATCH --error=/leonardo_work/EUHPC_D29_022/mchiesa0/logs/qwen3_dafny_%j.err
#SBATCH --time=01:00:00
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=128G
#SBATCH --partition=boost_usr_prod
#SBATCH --qos=normal
#SBATCH --account=EUHPC_D29_022
#SBATCH --gres=gpu:1

set -e

module load cuda/12.3

MODEL="/leonardo_work/EUHPC_D29_022/mchiesa0/models/Qwen3-Coder-Next-GGUF/Qwen3-Coder-Next-UD-Q4_K_XL.gguf"
LLAMA_BIN="/leonardo_work/EUHPC_D29_022/mchiesa0/software/llama.cpp/build/bin"
SCRIPTS="/leonardo_work/EUHPC_D29_022/mchiesa0/scripts"
BENCHMARKS="/leonardo_work/EUHPC_D29_022/mchiesa0/benchmarks"
DAFNY="/leonardo_work/EUHPC_D29_022/mchiesa0/software/dafny/dafny"
Z3="/leonardo_work/EUHPC_D29_022/mchiesa0/software/z3/bin/z3"
PORT=8080
RESULTS_DIR="/leonardo_work/EUHPC_D29_022/mchiesa0/results/qwen3_dafny_${SLURM_JOB_ID}"

export LD_LIBRARY_PATH="${LLAMA_BIN}:${LD_LIBRARY_PATH}"
source /leonardo_work/EUHPC_D29_022/mchiesa0/software/sglang_env/bin/activate

mkdir -p "${RESULTS_DIR}"

echo "=== Starting Qwen3-Coder-Next Server ==="
echo "Job ID: ${SLURM_JOB_ID}"
nvidia-smi --query-gpu=name,memory.total,memory.free --format=csv

"${LLAMA_BIN}/llama-server" -m "${MODEL}" -ngl 999 -c 16384 --host 127.0.0.1 --port ${PORT} 2>&1 &
SERVER_PID=$!

echo "Waiting for server..."
for i in $(seq 1 900); do
    HEALTH=$(curl -s -o /dev/null -w "%{http_code}" http://127.0.0.1:${PORT}/health 2>/dev/null || echo "000")
    if [ "${HEALTH}" = "200" ]; then
        echo "Server ready after ${i}s"
        break
    fi
    if [ $((i % 60)) -eq 0 ]; then
        MEM=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader 2>/dev/null | head -1)
        echo "  Waiting... health=${HEALTH} mem=${MEM} (${i}s)"
    fi
    sleep 1
done

nvidia-smi --query-gpu=memory.used,memory.free --format=csv

echo "=== Running 4 Parallel Dafny Prover Jobs ==="
cd "${RESULTS_DIR}"

python "${SCRIPTS}/dafny_prover_llama.py" "${BENCHMARKS}/01_max_element.dfy" \
    --url "http://localhost:${PORT}" --dafny "${DAFNY}" --z3 "${Z3}" \
    --max-attempts 3 --log v1_run1.log -o v1_run1_verified.dfy &
PID1=$!

python "${SCRIPTS}/dafny_prover_llama.py" "${BENCHMARKS}/01_max_element.dfy" \
    --url "http://localhost:${PORT}" --dafny "${DAFNY}" --z3 "${Z3}" \
    --max-attempts 3 --log v1_run2.log -o v1_run2_verified.dfy &
PID2=$!

python "${SCRIPTS}/dafny_prover_llama.py" "${BENCHMARKS}/01_max_element_v2.dfy" \
    --url "http://localhost:${PORT}" --dafny "${DAFNY}" --z3 "${Z3}" \
    --max-attempts 3 --log v2_run1.log -o v2_run1_verified.dfy &
PID3=$!

python "${SCRIPTS}/dafny_prover_llama.py" "${BENCHMARKS}/01_max_element_v2.dfy" \
    --url "http://localhost:${PORT}" --dafny "${DAFNY}" --z3 "${Z3}" \
    --max-attempts 3 --log v2_run2.log -o v2_run2_verified.dfy &
PID4=$!

echo "Started PIDs: ${PID1} ${PID2} ${PID3} ${PID4}"
wait ${PID1}; E1=$?
wait ${PID2}; E2=$?
wait ${PID3}; E3=$?
wait ${PID4}; E4=$?

echo "=== Results ==="
echo "V1 Run1: ${E1}, V1 Run2: ${E2}, V2 Run1: ${E3}, V2 Run2: ${E4}"

for log in v1_run1.log v1_run2.log v2_run1.log v2_run2.log; do
    echo "--- ${log} ---"
    grep -E "SUCCESS|FAILED|attempt" "${log}" 2>/dev/null | tail -3 || echo "(empty)"
done

kill ${SERVER_PID} 2>/dev/null || true
echo "Done! Results: ${RESULTS_DIR}"
