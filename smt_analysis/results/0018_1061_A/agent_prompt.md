Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Coins
You have unlimited number of coins with values $$$1, 2, \ldots, n$$$. You want to select some set of coins having the total value of $$$S$$$.

It is allowed to have multiple coins with the same value in the set. What is the minimum number of coins required to get sum $$$S$$$?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0018_1061_A/task.dfy

```dafny
// ── Formal Specification for the Coins Problem ──

// Sum of a sequence of integers.
ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

// Every coin has a denomination in {1, ..., n}.
ghost predicate AllValid(coins: seq<int>, n: int)
{
  forall i | 0 <= i < |coins| :: 1 <= coins[i] <= n
}

// A valid coin selection: non-empty, all denominations in {1..n}, summing to S.
ghost predicate IsValidSelection(coins: seq<int>, n: int, S: int)
{
  |coins| >= 1 && AllValid(coins, n) && Sum(coins) == S
}

// Exactly k coins from {1, ..., n} can achieve sum S iff S lies in [k, k*n].
// Each coin contributes at least 1 (minimum denomination) and at most n
// (maximum denomination), so k coins yield a sum in [k, k*n].
// Every integer in that range is achievable.
ghost predicate Achievable(k: int, n: int, S: int)
{
  k >= 1 && n >= 1 && k <= S && S <= k * n
}

// Constructive witness for Achievable: use (k-1) coins of denomination n,
// plus one coin carrying the remainder S - (k-1)*n, which lies in [1, n]
// whenever Achievable(k, n, S) holds.
ghost function Witness(k: int, n: int, S: int): seq<int>
{
  if k >= 1 && n >= 1 && k <= S && S <= k * n then
    seq(k, i requires 0 <= i < k => if i < k - 1 then n else S - (k - 1) * n)
  else
    []
}

// ── Method with contracts ──

method Coins(n: int, S: int) returns (minCoins: int)
  requires n >= 1
  requires S >= 1
  // Existence: minCoins coins from {1, ..., n} can achieve sum S
  ensures Achievable(minCoins, n, S)
  // Minimality: no fewer coins can achieve sum S
  ensures forall k | 1 <= k < minCoins :: !Achievable(k, n, S)
{
  minCoins := (S - 1) / n + 1;
}

// ── Tests ──
```

## Instructions:

1. Read the code carefully. Understand what the method does and what the spec requires.

2. Add loop invariants for every loop. Common patterns:
   - Bounds: `invariant 0 <= i <= |s|`
   - Accumulator: `invariant acc == F(s[..i])` for recursive ghost functions
   - Sequence slicing: `assert s[..i+1] == s[..i] + [s[i]];` before using F(s[..i+1])
   - Full slice identity: `assert s[..|s|] == s;` after loops that process entire sequences
   - Type preservation: `invariant AllNonNeg(s[..i])` if needed by the spec

3. Add helper lemmas if needed (e.g., SumAppend, induction lemmas).

4. Run dafny verify:
   ```bash
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0018_1061_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0018_1061_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0018_1061_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0018_1061_A/ (create the directory if needed).
