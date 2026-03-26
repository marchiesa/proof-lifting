# Dafny Benchmark Dataset from Codeforces

## Pipeline (per problem)

1. Parse problem statement
2. Parse code (Python/C++ solution)
3. Translate to Dafny implementation (no verification, just code)
4. Test implementation: `dafny run --no-verify` until correct
5. Write formal spec (non-ghost, bounded quantifiers) and test it: `dafny run --no-verify`
6. Timeout: 5 minutes per problem. Failures go to `queue/` for later

## Data Source

- HuggingFace: `open-r1/codeforces` (9,556 problems)
- HuggingFace: `open-r1/codeforces-submissions` (solutions, 36 shards, ~5.5GB)
- After filtering (has tests, not interactive, has rating): 9,023 problems
- Saved to `codeforces_data/problems.json`
- Python submissions being downloaded to `codeforces_data/python_submissions.json`

## Output per problem

```
dataset/NNN_problem_id/
  problem.txt       -- original problem statement
  solution.py       -- Python solution from Codeforces
  tests.json        -- input/output test cases
  task.dfy          -- Dafny implementation + formal spec (no invariants)
  tests.dfy         -- runtime tests for BOTH impl and spec
```

No reference.dfy. That's what the benchmark measures (LLM adds invariants).

## Current Step

- [x] Download Codeforces problems (9,023 saved to `codeforces_data/problems.json`)
- [x] Download Python submissions (2,000 matched to `codeforces_data/python_submissions.json`)
- [x] Write pipeline script (`pipeline.py`) — calls `claude -p` per problem
- [ ] Test on 1 problem
- [ ] Run on first 10 as pilot
- [ ] Scale up

## Dafny Command

```
/opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll
```

## Rules

- NEVER use `dafny verify` during dataset creation
- Only `dafny run --no-verify` for testing
- Formal spec must be non-ghost with bounded quantifiers (compilable)
- 5 min timeout per problem, queue failures
