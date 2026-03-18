Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Add Odd or Subtract Even
You are given two positive integers $$$a$$$ and $$$b$$$.

In one move, you can change $$$a$$$ in the following way:

- Choose any positive odd integer $$$x$$$ ($$$x > 0$$$) and replace $$$a$$$ with $$$a+x$$$;
- choose any positive even integer $$$y$$$ ($$$y > 0$$$) and replace $$$a$$$ with $$$a-y$$$.

You can perform as many such operations as you want. You can choose the same numbers $$$x$$$ and $$$y$$$ in different moves.

Your task is to find the minimum number of moves required to obtain $$$b$$$ from $$$a$$$. It is guaranteed that you can always obtain $$$b$$$ from $$$a$$$.

You have to answer $$$t$$$ independent test cases.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0097_1311_A/task.dfy

```dafny
// A single legal move: add a positive odd integer, or subtract a positive even integer.
ghost predicate ValidStep(from: int, to: int) {
  // Add positive odd: to = from + x, x >= 1, x odd
  (to > from && (to - from) % 2 == 1)
  ||
  // Subtract positive even: to = from - y, y >= 2, y even
  (from - to >= 2 && (from - to) % 2 == 0)
}

// Can we transform a into b using exactly `steps` legal moves?
// Base cases handle 0 and 1 step directly.
// For steps >= 2, there exists some intermediate value c reachable
// in one valid step from a, with the remainder reachable from c.
ghost predicate ReachableIn(a: int, b: int, steps: nat)
  decreases steps
{
  if steps == 0 then
    a == b
  else if steps == 1 then
    ValidStep(a, b)
  else
    exists c :: ValidStep(a, c) && ReachableIn(c, b, steps - 1)
}

method AddOddOrSubtractEven(a: int, b: int) returns (moves: int)
  requires a >= 1 && b >= 1
  ensures 0 <= moves <= 2
  ensures ReachableIn(a, b, moves)
  ensures forall k | 0 <= k < moves :: !ReachableIn(a, b, k)
{
  if a == b {
    moves := 0;
  } else if a % 2 == b % 2 && a > b {
    moves := 1;
  } else if a % 2 != b % 2 && b > a {
    moves := 1;
  } else {
    moves := 2;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0097_1311_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0097_1311_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0097_1311_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0097_1311_A/ (create the directory if needed).
