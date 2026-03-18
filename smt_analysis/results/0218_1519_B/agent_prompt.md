Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: The Cake Is a Lie
There is a $$$n \times m$$$ grid. You are standing at cell $$$(1, 1)$$$ and your goal is to finish at cell $$$(n, m)$$$.

You can move to the neighboring cells to the right or down. In other words, suppose you are standing at cell $$$(x, y)$$$. You can:

- move right to the cell $$$(x, y + 1)$$$ — it costs $$$x$$$ burles;
- move down to the cell $$$(x + 1, y)$$$ — it costs $$$y$$$ burles.

Can you reach cell $$$(n, m)$$$ spending exactly $$$k$$$ burles?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0218_1519_B/task.dfy

```dafny
// Specification: Grid reachability with exact cost.
//
// On an n × m grid, from cell (x, y) you can:
//   - move right to (x, y+1), paying x burles
//   - move down to (x+1, y), paying y burles
//
// CanReach(x, y, n, m, cost) is true iff there exists a sequence of such moves
// leading from (x, y) to (n, m) with total cost exactly equal to `cost`.
ghost predicate CanReach(x: int, y: int, n: int, m: int, cost: int)
  requires 1 <= x <= n && 1 <= y <= m
  decreases (n - x) + (m - y)
{
  // Already at the destination with zero remaining cost
  (x == n && y == m && cost == 0)
  ||
  // Move right from (x, y) to (x, y+1), paying x burles
  (y < m && CanReach(x, y + 1, n, m, cost - x))
  ||
  // Move down from (x, y) to (x+1, y), paying y burles
  (x < n && CanReach(x + 1, y, n, m, cost - y))
}

method {:verify false} TheCakeIsALie(n: int, m: int, k: int) returns (result: bool)
  requires n >= 1 && m >= 1
  ensures result == CanReach(1, 1, n, m, k)
{
  var remaining := k - (1 * (m - 1) + m * (n - 1));
  result := remaining == 0;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0218_1519_B/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0218_1519_B/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0218_1519_B/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0218_1519_B/ (create the directory if needed).
