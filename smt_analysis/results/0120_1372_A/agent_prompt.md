Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Omkar and Completion
You have been blessed as a child of Omkar. To express your gratitude, please solve this problem for Omkar!

An array $$$a$$$ of length $$$n$$$ is called complete if all elements are positive and don't exceed $$$1000$$$, and for all indices $$$x$$$,$$$y$$$,$$$z$$$ ($$$1 \leq x,y,z \leq n$$$), $$$a_{x}+a_{y} \neq a_{z}$$$ (not necessarily distinct).

You are given one integer $$$n$$$. Please find any complete array of length $$$n$$$. It is guaranteed that under given constraints such array exists.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0120_1372_A/task.dfy

```dafny
ghost predicate InRange(a: seq<int>)
{
  forall i | 0 <= i < |a| :: 1 <= a[i] <= 1000
}

ghost predicate NoTripleSum(a: seq<int>)
{
  forall x, y, z | 0 <= x < |a| && 0 <= y < |a| && 0 <= z < |a| ::
    a[x] + a[y] != a[z]
}

ghost predicate IsComplete(a: seq<int>)
{
  InRange(a) && NoTripleSum(a)
}

method Solve(n: int) returns (a: seq<int>)
  requires n >= 0
  ensures |a| == n
  ensures IsComplete(a)
{
  a := [];
  var i := 0;
  while i < n
  {
    a := a + [1];
    i := i + 1;
  }
}

method TestSolve(ns: seq<int>)
  requires forall i | 0 <= i < |ns| :: ns[i] >= 0
{
  for i := 0 to |ns| {
    var r := Solve(ns[i]);
    expect |r| == ns[i];
    for j := 0 to |r| {
      expect r[j] == 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0120_1372_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0120_1372_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0120_1372_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0120_1372_A/ (create the directory if needed).
