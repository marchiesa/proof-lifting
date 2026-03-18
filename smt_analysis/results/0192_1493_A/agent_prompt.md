Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Anti-knapsack
You are given two integers $$$n$$$ and $$$k$$$. You are asked to choose maximum number of distinct integers from $$$1$$$ to $$$n$$$ so that there is no subset of chosen numbers with sum equal to $$$k$$$.

A subset of a set is a set that can be obtained from initial one by removing some (possibly all or none) elements of it.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0192_1493_A/task.dfy

```dafny
// --- Formal specification predicates ---

ghost predicate AllDistinct(s: seq<int>)
{
  forall i, j | 0 <= i < |s| && 0 <= j < |s| && i != j :: s[i] != s[j]
}

ghost predicate AllInRange(s: seq<int>, n: int)
{
  forall i | 0 <= i < |s| :: 1 <= s[i] <= n
}

ghost predicate Contains(s: seq<int>, x: int)
{
  exists i | 0 <= i < |s| :: s[i] == x
}

// The set of all sums achievable by selecting any subset of elements from s.
// At each step we either include or exclude the last element.
ghost function AchievableSums(s: seq<int>): set<int>
  decreases |s|
{
  if |s| == 0 then {0}
  else
    var prev := AchievableSums(s[..|s|-1]);
    prev + set x | x in prev :: x + s[|s|-1]
}

// No subset of chosen has sum exactly equal to target
ghost predicate NoSubsetSumsTo(chosen: seq<int>, target: int)
{
  target !in AchievableSums(chosen)
}

// A valid anti-knapsack selection: distinct elements from {1..n}, no subset sums to k
ghost predicate IsValidSelection(chosen: seq<int>, n: int, k: int)
{
  AllDistinct(chosen) && AllInRange(chosen, n) && NoSubsetSumsTo(chosen, k)
}

// Maximal: every element from {1..n} not already chosen would create a subset summing to k
ghost predicate IsMaximal(chosen: seq<int>, n: int, k: int)
{
  forall x | 1 <= x <= n && !Contains(chosen, x) ::
    k in AchievableSums(chosen + [x])
}

// --- Method with formal specification ---

method AntiKnapsack(n: int, k: int) returns (chosen: seq<int>)
  requires 1 <= k <= n
  ensures IsValidSelection(chosen, n, k)
  ensures IsMaximal(chosen, n, k)
{
  chosen := [];
  var i := k + 1;
  while i <= n {
    chosen := chosen + [i];
    i := i + 1;
  }
  i := (k + 1) / 2;
  while i <= k - 1 {
    chosen := chosen + [i];
    i := i + 1;
  }
}

// --- Tests with runtime spec verification ---

method TestAntiKnapsack(n: int, k: int, expected: seq<int>)
  requires 1 <= k <= n
{
  var chosen := AntiKnapsack(n, k);
  expect chosen == expected;
  expect IsValidSelection(chosen, n, k);
  expect IsMaximal(chosen, n, k);
}
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0192_1493_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0192_1493_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0192_1493_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0192_1493_A/ (create the directory if needed).
