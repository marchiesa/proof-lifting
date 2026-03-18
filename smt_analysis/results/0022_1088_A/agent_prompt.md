Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Ehab and another construction problem
Given an integer $$$x$$$, find 2 integers $$$a$$$ and $$$b$$$ such that:

- $$$1 \le a,b \le x$$$
- $$$b$$$ divides $$$a$$$ ($$$a$$$ is divisible by $$$b$$$).
- $$$a \cdot b>x$$$.
- $$$\frac{a}{b}<x$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0022_1088_A/task.dfy

```dafny
ghost predicate ValidPair(a: int, b: int, x: int)
{
  1 <= a <= x &&
  1 <= b <= x &&
  a % b == 0 &&
  a * b > x &&
  a / b < x
}

ghost predicate SolutionExists(x: int)
{
  exists a :: exists b :: ValidPair(a, b, x)
}

method EhabConstruction(x: int) returns (a: int, b: int, found: bool)
  ensures found ==> ValidPair(a, b, x)
  ensures !found ==> !SolutionExists(x)
{
  a := 0;
  b := 0;
  found := false;

  var ai := 1;
  while ai <= x && !found
  {
    var bi := 1;
    while bi <= ai && !found
    {
      if ai % bi == 0 && ai * bi > x && ai / bi < x {
        a := ai;
        b := bi;
        found := true;
      }
      bi := bi + 1;
    }
    ai := ai + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0022_1088_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0022_1088_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0022_1088_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0022_1088_A/ (create the directory if needed).
