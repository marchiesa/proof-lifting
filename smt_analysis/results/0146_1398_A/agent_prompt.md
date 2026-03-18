Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Bad Triangle
You are given an array $$$a_1, a_2, \dots , a_n$$$, which is sorted in non-decreasing order ($$$a_i \le a_{i + 1})$$$.

Find three indices $$$i$$$, $$$j$$$, $$$k$$$ such that $$$1 \le i < j < k \le n$$$ and it is impossible to construct a non-degenerate triangle (a triangle with nonzero area) having sides equal to $$$a_i$$$, $$$a_j$$$ and $$$a_k$$$ (for example it is possible to construct a non-degenerate triangle with sides $$$3$$$, $$$4$$$ and $$$5$$$ but impossible with sides $$$3$$$, $$$4$$$ and $$$7$$$). If it is impossible to find such triple, report it.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0146_1398_A/task.dfy

```dafny
ghost predicate CanFormTriangle(x: int, y: int, z: int)
{
  x + y > z && x + z > y && y + z > x
}

ghost predicate Sorted(a: seq<int>)
{
  forall i, j | 0 <= i && i <= j && j < |a| :: a[i] <= a[j]
}

method BadTriangle(a: seq<int>) returns (result: (int, int, int), found: bool)
  requires |a| >= 3
  requires Sorted(a)
  ensures found ==>
    1 <= result.0 && result.0 < result.1 && result.1 < result.2 && result.2 <= |a| &&
    !CanFormTriangle(a[result.0 - 1], a[result.1 - 1], a[result.2 - 1])
  ensures !found ==>
    forall i, j, k | 0 <= i && i < j && j < k && k < |a| ::
      CanFormTriangle(a[i], a[j], a[k])
{
  result := (0, 0, 0);
  found := false;
  var n := |a|;

  var x := a[0] + a[1] - a[n - 1];
  var y := a[0] - a[1] + a[n - 1];
  var z := -a[0] + a[1] + a[n - 1];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (1, 2, n);
    found := true;
    return;
  }

  x := a[0] + a[n - 1] - a[n - 2];
  y := a[0] - a[n - 1] + a[n - 2];
  z := -a[0] + a[n - 1] + a[n - 2];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (1, n - 1, n);
    found := true;
    return;
  }

  x := a[0] + a[1] - a[2];
  y := a[0] - a[1] + a[2];
  z := -a[0] + a[1] + a[2];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (1, 2, 3);
    found := true;
    return;
  }

  x := a[n - 3] + a[n - 2] - a[n - 1];
  y := a[n - 3] - a[n - 2] + a[n - 1];
  z := -a[n - 3] + a[n - 2] + a[n - 1];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (n - 2, n - 1, n);
    found := true;
    return;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0146_1398_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0146_1398_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0146_1398_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0146_1398_A/ (create the directory if needed).
