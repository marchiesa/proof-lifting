Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Three Pairwise Maximums
You are given three positive (i.e. strictly greater than zero) integers $$$x$$$, $$$y$$$ and $$$z$$$.

Your task is to find positive integers $$$a$$$, $$$b$$$ and $$$c$$$ such that $$$x = \max(a, b)$$$, $$$y = \max(a, c)$$$ and $$$z = \max(b, c)$$$, or determine that it is impossible to find such $$$a$$$, $$$b$$$ and $$$c$$$.

You have to answer $$$t$$$ independent test cases. Print required $$$a$$$, $$$b$$$ and $$$c$$$ in any (arbitrary) order.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0132_1385_A/task.dfy

```dafny
ghost function MaxOf(a: int, b: int): int {
  if a > b then a else b
}

ghost function MinOf(a: int, b: int): int {
  if a < b then a else b
}

// A valid solution: positive a, b, c whose pairwise maxima are exactly x, y, z
ghost predicate IsValidSolution(x: int, y: int, z: int, a: int, b: int, c: int) {
  a > 0 && b > 0 && c > 0 &&
  MaxOf(a, b) == x && MaxOf(a, c) == y && MaxOf(b, c) == z
}

// Does any valid solution exist?
ghost predicate SolutionExists(x: int, y: int, z: int)
  requires x > 0 && y > 0 && z > 0
{
  exists a ::
    exists b ::
      exists c ::
        IsValidSolution(x, y, z, a, b, c)
}

method ThreePairwiseMaximums(x: int, y: int, z: int) returns (possible: bool, a: int, b: int, c: int)
  requires x > 0 && y > 0 && z > 0
  ensures possible == SolutionExists(x, y, z)
  ensures possible ==> IsValidSolution(x, y, z, a, b, c)
{
  var m := x;
  if y > m { m := y; }
  if z > m { m := z; }

  var cnt := 0;
  if x == m { cnt := cnt + 1; }
  if y == m { cnt := cnt + 1; }
  if z == m { cnt := cnt + 1; }

  if cnt >= 2 {
    possible := true;
    a := if x <= y then x else y;
    b := if x <= z then x else z;
    c := if y <= z then y else z;
  } else {
    possible := false;
    a := 0;
    b := 0;
    c := 0;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0132_1385_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0132_1385_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0132_1385_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0132_1385_A/ (create the directory if needed).
