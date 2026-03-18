Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Array and Peaks
A sequence of $$$n$$$ integers is called a permutation if it contains all integers from $$$1$$$ to $$$n$$$ exactly once.

Given two integers $$$n$$$ and $$$k$$$, construct a permutation $$$a$$$ of numbers from $$$1$$$ to $$$n$$$ which has exactly $$$k$$$ peaks. An index $$$i$$$ of an array $$$a$$$ of size $$$n$$$ is said to be a peak if $$$1 < i < n$$$ and $$$a_i \gt a_{i-1}$$$ and $$$a_i \gt a_{i+1}$$$. If such permutation is not possible, then print $$$-1$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0208_1513_A/task.dfy

```dafny
/* === Specification: structural predicates modeling the problem === */

// A sequence is a permutation of {1, ..., n}: length n, all values
// in [1..n], and all values distinct.
ghost predicate IsPermutation(a: seq<int>, n: int)
{
  |a| == n && n >= 1 &&
  (forall i | 0 <= i < n :: 1 <= a[i] <= n) &&
  (forall i, j | 0 <= i < j < n :: a[i] != a[j])
}

// Position i is a peak: it is strictly interior and strictly greater
// than both its immediate neighbors.
ghost predicate IsPeak(a: seq<int>, i: int)
{
  0 < i < |a| - 1 && a[i] > a[i - 1] && a[i] > a[i + 1]
}

// Count the number of peaks in a sequence (slice-based recursion).
ghost function CountPeaks(a: seq<int>): int
  decreases |a|
{
  if |a| <= 2 then 0
  else CountPeaks(a[..|a| - 1]) + (if IsPeak(a, |a| - 2) then 1 else 0)
}

// Upper bound on peaks in any permutation of size n.
// Peaks must occupy interior positions (0 < i < n-1) and no two peaks
// can be adjacent — a[i] > a[i+1] and a[i+1] > a[i] is contradictory.
// This equals the maximum independent set on the path of (n-2)
// interior vertices, i.e. floor((n-1)/2).
ghost function MaxPeaks(n: int): int
{
  if n < 1 then 0 else (n - 1) / 2
}

/* === Method with specification === */

method ArrayAndPeaks(n: int, k: int) returns (result: seq<int>, possible: bool)
  ensures possible ==> IsPermutation(result, n) && CountPeaks(result) == k
  ensures !possible ==> result == [] && (n < 1 || k < 0 || k > MaxPeaks(n))
{
  var ma := (n - 1) / 2;
  if k > ma || k < 0 || n < 1 {
    result := [];
    possible := false;
  } else {
    var ans := new int[n];
    var idx := 0;
    while idx < n {
      ans[idx] := 0;
      idx := idx + 1;
    }

    var c := 0;
    var i := 1;
    while i < n && c < k {
      ans[i] := n - c;
      c := c + 1;
      i := i + 2;
    }

    var j := 1;
    i := 0;
    while i < n {
      if ans[i] == 0 {
        ans[i] := j;
        j := j + 1;
      }
      i := i + 1;
    }

    result := ans[..];
    possible := true;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0208_1513_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0208_1513_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0208_1513_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0208_1513_A/ (create the directory if needed).
