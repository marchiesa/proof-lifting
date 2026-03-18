Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: C+=
Leo has developed a new programming language C+=. In C+=, integer variables can only be changed with a "+=" operation that adds the right-hand side value to the left-hand side variable. For example, performing "a += b" when a = $$$2$$$, b = $$$3$$$ changes the value of a to $$$5$$$ (the value of b does not change).

In a prototype program Leo has two integer variables a and b, initialized with some positive values. He can perform any number of operations "a += b" or "b += a". Leo wants to test handling large integers, so he wants to make the value of either a or b strictly greater than a given value $$$n$$$. What is the smallest number of operations he has to perform?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0127_1368_A/task.dfy

```dafny
// Whether either variable strictly exceeds the threshold n
ghost predicate Exceeds(a: int, b: int, n: int) {
  a > n || b > n
}

// Whether it is possible to make either variable exceed n starting from (a, b)
// using at most `steps` operations, where each operation is either
// "a += b" (producing (a+b, b)) or "b += a" (producing (a, b+a)).
ghost predicate Reachable(a: int, b: int, n: int, steps: nat)
  decreases steps
{
  Exceeds(a, b, n) ||
  (steps > 0 && (Reachable(a + b, b, n, steps - 1) || Reachable(a, b + a, n, steps - 1)))
}

method CPlusEqual(a: int, b: int, n: int) returns (ops: int)
  requires a > 0 && b > 0 && n > 0
  requires a <= n && b <= n
  ensures ops >= 1 && Reachable(a, b, n, ops) && !Reachable(a, b, n, ops - 1)
{
  var x := a;
  var y := b;
  if x > y {
    x, y := y, x;
  }
  var i := 1;
  while i < 1000 {
    if i % 2 == 1 {
      x := x + y;
    } else {
      y := y + x;
    }
    if x > n || y > n {
      ops := i;
      return;
    }
    i := i + 1;
  }
  ops := 0;
  return;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0127_1368_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0127_1368_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0127_1368_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0127_1368_A/ (create the directory if needed).
