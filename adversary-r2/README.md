# Adversary Round 2: Verification Benchmarks

## Design Philosophy

Round 1 revealed the prover's weaknesses:
- **DP optimality proofs** are genuinely hard (prover FAILED on min coin change)
- **Graph reasoning** is stressful (BFS reachability took 10 attempts)
- **Long lemma chains** with nested quantifiers overwhelm the prover

Round 2 exploits ALL of these weaknesses simultaneously. Every problem requires proving **optimality** (not just feasibility), which demands complex inductive lemmas, exchange arguments, or greedy-stays-ahead proofs.

## Problems

| # | Problem | Algorithm | Why It's Hard |
|---|---------|-----------|--------------|
| 1 | 0/1 Knapsack | 2D DP | Optimality over all 2^n subsets; two-dimensional induction |
| 2 | Longest Increasing Subsequence | O(n^2) DP | Quantification over all exponentially many subsequences |
| 3 | Edit Distance | 2D DP | Optimality over infinite space of edit operation sequences |
| 4 | Dijkstra's Shortest Path | Greedy + graph | Graph path reasoning + greedy optimality + unreachability |
| 5 | Topological Sort + Cycle Detection | Kahn's BFS | Cycle existence proof (constructive) + DAG completeness |
| 6 | Interval Scheduling | Greedy sort-by-end | Exchange argument: greedy dominates all alternatives step-by-step |

## Difficulty Expectations

- **Problems 1-3** (DP optimality): The prover failed on min coin change in round 1. These are structurally similar but with added complexity (2D tables, subsequences, edit sequences). Expected: FAIL or need assume {:axiom}.
- **Problem 4** (Dijkstra): Combines graph reasoning (which took 10 attempts for BFS) with shortest-path optimality. Expected: FAIL.
- **Problem 5** (Topological Sort): Cycle detection completeness requires constructive cycle extraction from DFS state. Expected: VERY HARD.
- **Problem 6** (Interval Scheduling): Exchange arguments are a different proof paradigm the prover hasn't seen. Expected: FAIL or barely pass.

## Verification

```bash
# Verify a problem parses (will have verification errors, not syntax errors):
/opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify adversary-r2/problems/N/task.dfy
```

## File Structure

Each problem directory contains:
- `description.md` - Problem description and difficulty analysis
- `task.dfy` - Dafny file with specs + algorithm code (NO invariants/lemmas)
- `tests.dfy` - Test file with concrete examples
