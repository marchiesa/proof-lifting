Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Even Subset Sum Problem
You are given an array $$$a$$$ consisting of $$$n$$$ positive integers. Find a non-empty subset of its elements such that their sum is even (i.e. divisible by $$$2$$$) or determine that there is no such subset.

Both the given array and required subset may contain equal values.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0093_1323_A/task.dfy

```dafny
ghost function Pow2(n: int): int
  decreases if n < 0 then 0 else n
{
  if n <= 0 then 1 else 2 * Pow2(n - 1)
}

ghost predicate BitSet(mask: int, i: int)
{
  mask >= 0 && i >= 0 && (mask / Pow2(i)) % 2 == 1
}

ghost function MaskedSum(a: seq<int>, mask: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else MaskedSum(a[..|a| - 1], mask) + (if BitSet(mask, |a| - 1) then a[|a| - 1] else 0)
}

ghost predicate HasEvenSubset(a: seq<int>)
{
  exists mask: int :: mask >= 1 && MaskedSum(a, mask) % 2 == 0
}

ghost predicate Distinct(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] != s[j]
}

ghost predicate ValidIndices(indices: seq<int>, n: int)
{
  |indices| > 0 &&
  Distinct(indices) &&
  (forall i | 0 <= i < |indices| :: 1 <= indices[i] <= n)
}

ghost function IndexSum(a: seq<int>, indices: seq<int>): int
  decreases |indices|
{
  if |indices| == 0 then 0
  else
    var idx := indices[|indices| - 1];
    IndexSum(a, indices[..|indices| - 1]) + (if 1 <= idx <= |a| then a[idx - 1] else 0)
}

method EvenSubsetSum(a: seq<int>) returns (indices: seq<int>)
  requires |a| >= 1
  requires forall i | 0 <= i < |a| :: a[i] > 0
  ensures (indices == [-1]) <==> !HasEvenSubset(a)
  ensures indices != [-1] ==> ValidIndices(indices, |a|) && IndexSum(a, indices) % 2 == 0
{
  var n := |a|;
  if n == 1 && a[0] % 2 == 1 {
    indices := [-1];
  } else {
    var ind := -1;
    var ind2 := -1;
    var ind3 := -1;
    var j := 0;
    while j < n
    {
      if a[j] % 2 == 0 {
        ind := j;
      } else if ind2 == -1 {
        ind2 := j;
      } else {
        ind3 := j;
      }
      j := j + 1;
    }
    if ind == -1 {
      indices := [ind2 + 1, ind3 + 1];
    } else {
      indices := [ind + 1];
    }
  }
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0093_1323_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0093_1323_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0093_1323_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0093_1323_A/ (create the directory if needed).
