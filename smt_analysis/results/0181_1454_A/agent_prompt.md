Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Special Permutation
You are given one integer $$$n$$$ ($$$n > 1$$$).

Recall that a permutation of length $$$n$$$ is an array consisting of $$$n$$$ distinct integers from $$$1$$$ to $$$n$$$ in arbitrary order. For example, $$$[2, 3, 1, 5, 4]$$$ is a permutation of length $$$5$$$, but $$$[1, 2, 2]$$$ is not a permutation ($$$2$$$ appears twice in the array) and $$$[1, 3, 4]$$$ is also not a permutation ($$$n = 3$$$ but there is $$$4$$$ in the array).

Your task is to find a permutation $$$p$$$ of length $$$n$$$ that there is no index $$$i$$$ ($$$1 \le i \le n$$$) such that $$$p_i = i$$$ (so, for all $$$i$$$ from $$$1$$$ to $$$n$$$ the condition $$$p_i \ne i$$$ should be satisfied).

You have to answer $$$t$$$ independent test cases.

If there are several answers, you can print any. It can be proven that the answer exists for each $$$n > 1$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0181_1454_A/task.dfy

```dafny
ghost predicate InRange(p: seq<int>, n: int)
{
  forall i | 0 <= i < |p| :: 1 <= p[i] <= n
}

ghost predicate AllDistinct(p: seq<int>)
{
  forall i, j | 0 <= i < |p| && 0 <= j < |p| && i != j :: p[i] != p[j]
}

ghost predicate IsPermutation(p: seq<int>, n: int)
{
  |p| == n && InRange(p, n) && AllDistinct(p)
}

ghost predicate NoFixedPoint(p: seq<int>)
{
  forall i | 0 <= i < |p| :: p[i] != i + 1
}

method SpecialPermutation(n: int) returns (p: seq<int>)
  requires n > 1
  ensures IsPermutation(p, n)
  ensures NoFixedPoint(p)
{
  p := [n];
  var i := 1;
  while i < n {
    p := p + [i];
    i := i + 1;
  }
}

method BuildExpected(n: int) returns (e: seq<int>)
{
  e := [n];
  var i := 1;
  while i < n {
    e := e + [i];
    i := i + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0181_1454_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0181_1454_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0181_1454_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0181_1454_A/ (create the directory if needed).
