# Running the Dafny Benchmark on Leonardo (CINECA)

This directory contains SLURM scripts for running the Dafny verification
benchmark at scale on the Leonardo supercomputer using vLLM-served models on
A100 GPUs.

## Prerequisites

### 1. Python environment

Create a virtual environment on the shared filesystem and install dependencies:

```bash
module load python/3.11 cuda/12.1

python -m venv /path/to/shared/.venv
source /path/to/shared/.venv/bin/activate

pip install vllm requests pyyaml tqdm
```

### 2. Dafny installation

Dafny must be available on the compute nodes.  You can either:

- Pre-install it on the shared filesystem, or
- Set `DAFNY_CMD` in `leonardo_job.sh` to point at a working binary.

### 3. Model access

If using a gated model (e.g. Llama 3.1), make sure your HuggingFace token is
set:

```bash
export HF_TOKEN=hf_...
# or
huggingface-cli login
```

## How to run

### Small run (single GPU, small model)

```bash
export MODEL=meta-llama/Llama-3.1-8B-Instruct
export TP_SIZE=1

sbatch --gres=gpu:1 --ntasks-per-node=1 --mem=120G --time=01:00:00 leonardo_job.sh
```

### Medium run (4 GPUs, 70B model with TP=2)

```bash
export MODEL=meta-llama/Llama-3.1-70B-Instruct
export TP_SIZE=2

sbatch leonardo_job.sh
```

This allocates 4 GPUs and starts 2 vLLM servers (each using 2 GPUs for tensor
parallelism).

### Large run (multi-node)

```bash
export MODEL=meta-llama/Llama-3.1-70B-Instruct
export TP_SIZE=4

sbatch --nodes=2 --ntasks-per-node=4 --gres=gpu:4 --time=08:00:00 leonardo_job.sh
```

## Configuring for different models

Edit the `MODEL` environment variable (or export it before `sbatch`):

| Model | TP_SIZE | GPUs needed |
|-------|---------|-------------|
| Llama-3.1-8B-Instruct | 1 | 1 |
| Llama-3.1-70B-Instruct | 2 | 2 |
| Llama-3.1-70B-Instruct (bf16) | 4 | 4 |
| Mixtral-8x7B-Instruct | 2 | 2 |
| CodeLlama-34B-Instruct | 1 | 1 (A100 80GB) |

## Collecting and analyzing results

Results are written to `$RESULTS_DIR` (defaults to
`benchmark/results/leonardo_<timestamp>/`).

After the job completes, analyze results locally:

```bash
# Copy results back (if needed)
scp -r leonardo:/path/to/results ./results/

# Analyze
python benchmark/analyze_results.py ./results/

# Or compare multiple runs
python benchmark/analyze_results.py ./results/run1/ ./results/run2/
```

Each run produces:
- `results.json` -- full structured results
- `results.csv` -- flat summary table

## Files

| File | Purpose |
|------|---------|
| `leonardo_job.sh` | Main SLURM batch script |
| `launch_vllm.sh` | Helper to start vLLM on a single GPU |
| `README.md` | This file |

## Troubleshooting

**vLLM fails to start**: Check `/tmp/vllm_gpu*_port*.log` on the compute node.
Common issues: insufficient GPU memory, missing model files, CUDA version
mismatch.

**OOM errors**: Reduce `TP_SIZE` or increase the number of GPUs.  For 70B
models, 2xA100-80GB is the minimum.

**Timeout waiting for server**: Large models can take 5-10 minutes to load.
The default timeout is 10 minutes.  Increase `MAX_WAIT` in `launch_vllm.sh` if
needed.

**Dafny not found**: Make sure `DAFNY_CMD` points to a valid Dafny installation
accessible from the compute nodes.
