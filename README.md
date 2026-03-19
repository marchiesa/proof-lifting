# SMT Quirk Analysis Pipeline

Automated pipeline for discovering and classifying SMT solver quirks in
verified Dafny programs. Given a set of competitive programming problems,
the pipeline generates verified Dafny code, identifies which proof
assertions are truly needed by the solver (vs. redundant), and classifies
each essential assertion by the underlying solver limitation.

## Pipeline Overview

```
Step 1: Dataset Generation     (pipeline.py)
    Codeforces problems → Dafny task.dfy + tests.dfy
        ↓
Step 2: Verification           (quirk_finder.py --verify-only)
    task.dfy → verified.dfy (LLM adds invariants/assertions)
        ↓
Step 3: Verification Check     (check_verified.py)
    verified.dfy → verified_problems.txt (filter to programs that pass)
        ↓
Step 4: Lemma Inlining         (inline_lemmas.py)
    verified.dfy → verified_inlined.dfy (inline non-recursive lemmas)
        ↓
Step 5: Ablation               (fast_diagnose.py --ablate-only)
    Remove each assertion one at a time → find essential assertions
        ↓
Step 6: Classification         (fast_diagnose.py --diagnose-only)
    Extract Z3 models → classify by SMT mechanism (A/B/C/D)
```

## Prerequisites

- [.NET 8 SDK](https://dotnet.microsoft.com/download/dotnet/8.0)
- [Z3](https://github.com/Z3Prover/z3) (tested with 4.15.x)
- Python 3.10+
- [Claude Code CLI](https://claude.ai/claude-code) (for steps 1 and 2)

## Setup

### 1. Clone this repo

```bash
git clone https://github.com/marchiesa/proof-lifting.git
cd proof-lifting
```

### 2. Clone and build modified Dafny

```bash
git clone -b proof-lifting https://github.com/marchiesa/dafny.git dafny-source
cd dafny-source
git submodule update --init --recursive
dotnet build Source/Dafny.sln
cd ..
```

### 3. Clone and build modified Boogie

```bash
git clone -b proof-lifting https://github.com/marchiesa/boogie.git boogie
cd boogie
dotnet build Source/Boogie.sln
cd ..
```

### 4. Set environment (only if `dotnet --version` is not 8.x)

```bash
export DOTNET8=/path/to/dotnet8
```

All scripts read `DOTNET8` (falls back to `DOTNET`, then `dotnet` in PATH).
If your default `dotnet` is already v8, no env var is needed.

## Running the Pipeline

### Quick start (reproduce results from existing data)

If you just want to reproduce the ablation and classification results
from the already-committed dataset (95 verified programs):

```bash
# Ablation: ~15 min with 5 workers
python3 smt_analysis/fast_diagnose.py --all --ablate-only --workers 5

# Classification: ~30 min with 5 workers
python3 smt_analysis/fast_diagnose.py --all --diagnose-only --workers 5
```

Expected output: 927 assertions, 191 essential, 40 problems with essential.

### Step 1: Dataset Generation

Generates Dafny problems from Codeforces. Each problem gets a method body
with formal spec (pre/postconditions) but no proof annotations.

```bash
python3 pipeline.py --start 0 --count 100 --workers 10 --max-rating 1600
```

**Requires:** Claude Code CLI (spawns one Claude instance per problem).

**Input:** `codeforces_data/problems.json`, `codeforces_data/python_submissions.json`

**Output per problem** (`dataset/{NNN}_{problem_id}/`):
- `task.dfy` — Dafny method + formal spec (no invariants/assertions)
- `tests.dfy` — runtime tests for implementation and spec

### Step 2: Verification

An LLM adds proof annotations (loop invariants, assertions, ghost
variables, lemmas) to make `dafny verify` pass.

```bash
# Verify all unverified problems
python3 smt_analysis/quirk_finder.py --all --verify-only --workers 5 --skip-verified

# Verify specific problems
python3 smt_analysis/quirk_finder.py --names 0000_1013_A --verify-only
```

**Requires:** Claude Code CLI.

**Output per problem** (`smt_analysis/results/{problem}/`):
- `verified.dfy` — annotated program that passes `dafny verify`
- `verify_result.json` — verification status and timing

### Step 3: Verification Check

Not all `verified.dfy` files actually verify (LLM may have false-positive
results, or the modified Dafny compiler may behave differently). This step
filters to only programs that cleanly pass.

```bash
python3 smt_analysis/check_verified.py
```

**Output:**
- `smt_analysis/results/verified_problems.txt` — list of problem IDs that pass
- `smt_analysis/results/verification_status.json` — full results per problem

All subsequent steps only process problems in `verified_problems.txt`.

### Step 4: Lemma Inlining

Non-recursive lemmas are essentially packaged assertions. Inlining them
makes ablation more granular: individual assertions within the lemma body
can be tested instead of the opaque lemma call.

```bash
# Inline for all verified problems
python3 smt_analysis/inline_lemmas.py --all --workers 5

# Dry run (show what would be inlined)
python3 smt_analysis/inline_lemmas.py --all --dry-run

# Specific problems
python3 smt_analysis/inline_lemmas.py --names 0006_1017_A
```

**Output:** `smt_analysis/results/{problem}/verified_inlined.dfy`

The script re-verifies after inlining and only keeps changes that pass.
If `verified_inlined.dfy` exists, the ablation pipeline uses it instead
of `verified.dfy`.

### Step 5: Ablation

For each assertion in method bodies, create a variant with that assertion
removed and run `dafny verify`. If verification fails, the assertion is
**essential** (the solver needs it). If verification passes, it is
**redundant**.

```bash
# All problems (~15 min with 5 workers)
python3 smt_analysis/fast_diagnose.py --all --ablate-only --workers 5

# Specific problems
python3 smt_analysis/fast_diagnose.py --names 0000_1013_A 0003_1028_A --ablate-only
```

**How it works:**
1. Generates an AST mapping (`--ast-mapping`) using the modified Dafny compiler
2. Extracts `assert` statements from method bodies (not lemma bodies, not invariants)
3. For each assertion, comments it out and runs `dafny verify` with 60s timeout
4. Handles `assert ... by { ... }` blocks as single units
5. Handles inline assertions (e.g., `if x { assert false; }`) by surgical text removal
6. Rejects parse errors and prover errors as non-essential

**Output per problem:**
- `ablation/results.json` — per-assertion essentiality (`essential: true/false`)
- `ablation/without_NN.dfy` — variant files with each assertion removed
- `fast_report.json` — summary with essential/non-essential counts

### Step 6: Classification

For each essential equality assertion, extract Z3's counterexample model
and classify the assertion by the underlying SMT mechanism.

```bash
# All problems (~30 min with 5 workers)
python3 smt_analysis/fast_diagnose.py --all --diagnose-only --workers 5

# Specific problems
python3 smt_analysis/fast_diagnose.py --names 0000_1013_A --diagnose-only
```

**How it works:**
1. For each essential equality assertion, runs Dafny → Boogie with `--bprint`
   on the variant (without that assertion)
2. Runs Boogie with `/printModel:1` to extract Z3's counterexample model
3. Pattern-matches assertion text against known B1 sub-patterns
   (take-full, take-append, take-of-take, etc.)
4. Analyzes the model for sequence extensionality gaps
   (same-length sequences with different object identity)
5. Non-equality assertions are flagged for manual classification

**Output per problem:**
- `fast_report.json` — updated with `diagnoses` array (category per assertion)
- `models/assert_NN/boogie_model.txt` — raw Z3 counterexample models

**Global output:**
- `smt_analysis/results/diagnosis_summary.json` — aggregate categories across all problems

### Running the Full Pipeline (steps 5+6 together)

```bash
# Without --ablate-only or --diagnose-only, both phases run sequentially
python3 smt_analysis/fast_diagnose.py --names 0000_1013_A
```

## Output Structure

```
smt_analysis/results/
    verified_problems.txt          # 95 problems that actually verify
    verification_status.json       # per-problem verification status
    diagnosis_summary.json         # aggregate classification results

    {problem_name}/
        verified.dfy               # annotated program (from step 2)
        verified_inlined.dfy       # with lemmas inlined (from step 4)
        verify_result.json         # verification status

        artifacts/
            ast_mapping.json       # Dafny → Boogie mapping
            output.bpl             # Boogie IL
            dafny_output.txt       # compiler output

        ablation/
            results.json           # per-assertion essentiality
            without_00.dfy         # variant without assertion 0
            without_01.dfy         # variant without assertion 1
            ...

        models/
            assert_00/
                boogie_model.txt   # Z3 counterexample model
                dafny_output.txt
            ...

        fast_report.json           # diagnosis with categories
```

## Current Results

- **95** verified programs (from 208 Codeforces problems)
- **927** total assertions in method bodies
- **191** essential assertions across **40** programs (21%)
- **736** redundant assertions (79%)

Automated classification categories:
- B1 sequence extensionality: 34 (pattern-matched) + 13 (model-confirmed) = 47
- Flagged (non-equality, needs manual A/C/D classification): 98
- Unknown equality with model: 48
- Unknown equality: 11

## Step 7: LLM Benchmark

Tests whether LLMs can recover the essential assertions that were stripped
from verified code. The LLM receives the code with assertions removed and
must add them back to make `dafny verify` pass. An AST-level comparison
ensures the LLM doesn't cheat by modifying the code or formal spec.

### Prepare inputs (local)

```bash
# Generates stripped.dfy, prompt.txt, reference_ast.json per problem
DOTNET8=/path/to/dotnet8 python3 smt_analysis/benchmark/prepare.py
```

### Deploy to Leonardo

```bash
bash smt_analysis/benchmark/deploy.sh
```

### Run on Leonardo

```bash
# Quick test (llama.cpp, 1 GPU, 3 problems)
sbatch $WORK/benchmark/launch_llama.sh "0024_1091_A 0068_1196_A 0012_1060_A"

# Full run (SGLang, 4 GPUs, all 40 problems)
sbatch $WORK/benchmark/launch_sglang.sh
```

### Integrity checks

The benchmark uses AST-level comparison (via modified Dafny's `--ast-mapping`)
to verify the LLM's output:

1. **Spec check**: all original functions/predicates/methods must exist with
   identical requires/ensures/invariants (new helper lemmas are OK)
2. **Body check**: all non-assert statements in each method must be identical
   to the original (asserts are excluded from comparison since those are what
   the LLM adds)

Any attempt that modifies code or spec is rejected, even if `dafny verify`
reports 0 errors.

### Results (gpt-oss-20b)

Committed in `smt_analysis/benchmark/results/gpt-oss-20b/`.

- 40 problems, 500s timeout, 1727 total attempts
- **9/40 pass (22.5%)**
- B1 (seq extensionality) problems: 0% pass rate
- A2 (predicate instantiation) problems: high pass rate
- 25.5% of attempts rejected by AST check (9% spec, 16.5% body)

### Placeholder experiment

A focused variant: instead of rewriting the whole program, the LLM sees
numbered placeholders where assertions were removed and outputs only the
assertions (as a JSON array). This tests "can the LLM guess WHAT is needed,
given WHERE it's needed?" — no code modification risk, per-assertion accuracy.

```bash
# Deploy (same inputs, different script)
scp smt_analysis/benchmark/run_placeholder.py $REMOTE:$BENCHMARK_DIR/

# Run on Leonardo (SGLang, 4 GPUs)
sbatch $WORK/benchmark/launch_placeholder_sglang.sh
```

## Proof Lifting (Dafny → Boogie → SMT mapping)

The pipeline uses modified Dafny and Boogie compilers that capture mappings
at each compilation stage:

```
Dafny source  →  Boogie IL  →  SMT-LIB  →  Z3
   (--ast-mapping)  (/nameMap)
```

### Modified Dafny ([marchiesa/dafny@proof-lifting](https://github.com/marchiesa/dafny/tree/proof-lifting))

`--ast-mapping output.json` maps Dafny constructs to Boogie:
variables, functions, invariants, assertions (with full expression ASTs).

Key file: `Source/DafnyCore/Verifier/AstMappingManager.cs`

### Modified Boogie ([marchiesa/boogie@proof-lifting](https://github.com/marchiesa/boogie/tree/proof-lifting))

`/nameMap:output.json` maps `$generated@@N` SMT names back to Boogie
identifiers, tracked per-VC (names are reused after `(reset)`).

Key files: `SMTLibLineariser.cs`, `SMTLibInteractiveTheoremProver.cs`

### Running the mapping chain directly

```bash
# Step 1: Dafny → Boogie + AST mapping
$DOTNET8 dafny-source/Binaries/Dafny.dll verify input.dfy \
    --ast-mapping ast_mapping.json --bprint output.bpl

# Step 2: Boogie → SMT + name mapping
$DOTNET8 boogie/Source/BoogieDriver/bin/Debug/net8.0/BoogieDriver.dll \
    output.bpl /proverLog:smt_input.smt2 /nameMap:name_map.json \
    /trackVerificationCoverage /normalizeNames:1

# Step 3: Z3
z3 smt_input.smt2
```

## Base Commits

- Dafny: `58b3f6a` (dafny-lang/dafny@master)
- Boogie: `3f38a63` (boogie-org/boogie@master)
