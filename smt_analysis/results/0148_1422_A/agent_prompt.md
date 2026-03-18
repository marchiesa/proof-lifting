Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Fence
Yura is tasked to build a closed fence in shape of an arbitrary non-degenerate simple quadrilateral. He's already got three straight fence segments with known lengths $$$a$$$, $$$b$$$, and $$$c$$$. Now he needs to find out some possible integer length $$$d$$$ of the fourth straight fence segment so that he can build the fence using these four segments. In other words, the fence should have a quadrilateral shape with side lengths equal to $$$a$$$, $$$b$$$, $$$c$$$, and $$$d$$$. Help Yura, find any possible length of the fourth side.

A non-degenerate simple quadrilateral is such a quadrilateral that no three of its corners lie on the same line, and it does not cross itself.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0148_1422_A/task.dfy

```dafny
// The generalized polygon inequality: each side of a quadrilateral
// must be strictly less than the sum of the other three sides.
// This is the necessary and sufficient condition for four positive
// lengths to form a non-degenerate simple quadrilateral.
ghost predicate QuadrilateralInequality(a: int, b: int, c: int, d: int)
{
  a < b + c + d &&
  b < a + c + d &&
  c < a + b + d &&
  d < a + b + c
}

ghost predicate CanFormQuadrilateral(a: int, b: int, c: int, d: int)
{
  a > 0 && b > 0 && c > 0 && d > 0 &&
  QuadrilateralInequality(a, b, c, d)
}

method Fence(a: int, b: int, c: int) returns (d: int)
  requires a > 0 && b > 0 && c > 0
  ensures d > 0
  ensures CanFormQuadrilateral(a, b, c, d)
{
  d := a + b + c - 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0148_1422_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0148_1422_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0148_1422_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0148_1422_A/ (create the directory if needed).
