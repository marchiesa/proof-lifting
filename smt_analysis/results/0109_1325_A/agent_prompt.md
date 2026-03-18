Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: EhAb AnD gCd
You are given a positive integer $$$x$$$. Find any such $$$2$$$ positive integers $$$a$$$ and $$$b$$$ such that $$$GCD(a,b)+LCM(a,b)=x$$$.

As a reminder, $$$GCD(a,b)$$$ is the greatest integer that divides both $$$a$$$ and $$$b$$$. Similarly, $$$LCM(a,b)$$$ is the smallest integer such that both $$$a$$$ and $$$b$$$ divide it.

It's guaranteed that the solution always exists. If there are several such pairs $$$(a, b)$$$, you can output any of them.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0109_1325_A/task.dfy

```dafny
ghost function Min(a: int, b: int): int {
  if a <= b then a else b
}

ghost function Max(a: int, b: int): int {
  if a >= b then a else b
}

ghost predicate Divides(d: int, n: int)
  requires d > 0
{
  n % d == 0
}

ghost predicate IsGcd(g: int, a: int, b: int)
  requires a > 0 && b > 0 && g > 0
{
  Divides(g, a) && Divides(g, b) &&
  forall d :: 1 <= d <= Min(a, b) ==> (Divides(d, a) && Divides(d, b)) ==> d <= g
}

ghost predicate IsLcm(l: int, a: int, b: int)
  requires a > 0 && b > 0 && l > 0
{
  Divides(a, l) && Divides(b, l) &&
  forall m :: 1 <= m <= l ==> (Divides(a, m) && Divides(b, m)) ==> l <= m
}

ghost predicate ValidSolution(a: int, b: int, x: int)
{
  a > 0 && b > 0 && x > 0 &&
  exists g | 1 <= g <= Min(a, b) ::
    exists l | Max(a, b) <= l <= a * b ::
      IsGcd(g, a, b) && IsLcm(l, a, b) && g + l == x
}

method EhAbAndGcd(x: int) returns (a: int, b: int)
  requires x >= 2
  ensures ValidSolution(a, b, x)
{
  a := 1;
  b := x - 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0109_1325_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0109_1325_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0109_1325_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0109_1325_A/ (create the directory if needed).
