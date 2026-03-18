Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Required Remainder
You are given three integers $$$x, y$$$ and $$$n$$$. Your task is to find the maximum integer $$$k$$$ such that $$$0 \le k \le n$$$ that $$$k \bmod x = y$$$, where $$$\bmod$$$ is modulo operation. Many programming languages use percent operator % to implement it.

In other words, with given $$$x, y$$$ and $$$n$$$ you need to find the maximum possible integer from $$$0$$$ to $$$n$$$ that has the remainder $$$y$$$ modulo $$$x$$$.

You have to answer $$$t$$$ independent test cases. It is guaranteed that such $$$k$$$ exists for each test case.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0155_1374_A/task.dfy

```dafny
ghost predicate InRange(k: int, n: int)
{
  0 <= k <= n
}

ghost predicate HasRemainder(k: int, x: int, y: int)
  requires x > 0
{
  k % x == y
}

ghost predicate IsMaxWithRemainder(k: int, x: int, y: int, n: int)
  requires x > 0
{
  InRange(k, n)
  && HasRemainder(k, x, y)
  && (forall k' :: 0 <= k' <= n ==> HasRemainder(k', x, y) ==> k' <= k)
}

method RequiredRemainder(x: int, y: int, n: int) returns (k: int)
  requires x > 0
  requires 0 <= y < x
  requires y <= n
  ensures IsMaxWithRemainder(k, x, y, n)
{
  var p := n % x;
  if p == y {
    k := n;
  } else if p > y {
    k := n - p + y;
  } else {
    k := n - p - (x - y);
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0155_1374_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0155_1374_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0155_1374_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0155_1374_A/ (create the directory if needed).
