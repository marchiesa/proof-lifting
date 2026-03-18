Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: The King's Race
On a chessboard with a width of $$$n$$$ and a height of $$$n$$$, rows are numbered from bottom to top from $$$1$$$ to $$$n$$$, columns are numbered from left to right from $$$1$$$ to $$$n$$$. Therefore, for each cell of the chessboard, you can assign the coordinates $$$(r,c)$$$, where $$$r$$$ is the number of the row, and $$$c$$$ is the number of the column.

The white king has been sitting in a cell with $$$(1,1)$$$ coordinates for a thousand years, while the black king has been sitting in a cell with $$$(n,n)$$$ coordinates. They would have sat like that further, but suddenly a beautiful coin fell on the cell with coordinates $$$(x,y)$$$...

Each of the monarchs wanted to get it, so they decided to arrange a race according to slightly changed chess rules:

As in chess, the white king makes the first move, the black king makes the second one, the white king makes the third one, and so on. However, in this problem, kings can stand in adjacent cells or even in the same cell at the same time.

The player who reaches the coin first will win, that is to say, the player who reaches the cell with the coordinates $$$(x,y)$$$ first will win.

Let's recall that the king is such a chess piece that can move one cell in all directions, that is, if the king is in the $$$(a,b)$$$ cell, then in one move he can move from $$$(a,b)$$$ to the cells $$$(a + 1,b)$$$, $$$(a - 1,b)$$$, $$$(a,b + 1)$$$, $$$(a,b - 1)$$$, $$$(a + 1,b - 1)$$$, $$$(a + 1,b + 1)$$$, $$$(a - 1,b - 1)$$$, or $$$(a - 1,b + 1)$$$. Going outside of the field is prohibited.

Determine the color of the king, who will reach the cell with the coordinates $$$(x,y)$$$ first, if the white king moves first.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0014_1075_A/task.dfy

```dafny
// ── Helper functions ──

ghost function Abs(x: int): int
{ if x >= 0 then x else -x }

ghost function Max(a: int, b: int): int
{ if a >= b then a else b }

// ── Problem formalization ──

// Chebyshev (L∞) distance between two cells
ghost function ChebyshevDist(r1: int, c1: int, r2: int, c2: int): int
{ Max(Abs(r1 - r2), Abs(c1 - c2)) }

// A valid single king move: to an adjacent cell (8 directions) within an n×n board
ghost predicate ValidKingStep(r1: int, c1: int, r2: int, c2: int, n: int)
{
  1 <= r1 <= n && 1 <= c1 <= n &&
  1 <= r2 <= n && 1 <= c2 <= n &&
  Abs(r1 - r2) <= 1 && Abs(c1 - c2) <= 1 &&
  (r1 != r2 || c1 != c2)
}

// Greedy one step toward (tr, tc): move each coordinate ±1 in the correct direction
ghost function StepToward(r: int, c: int, tr: int, tc: int): (int, int)
{
  (r + (if tr > r then 1 else if tr < r then -1 else 0),
   c + (if tc > c then 1 else if tc < c then -1 else 0))
}

// EXISTENCE witness: the greedy step is a valid king move that reduces the
// Chebyshev distance by exactly 1. Repeated application (induction on distance)
// constructs a valid king path of length ChebyshevDist.
ghost predicate GreedyStepValid(r: int, c: int, tr: int, tc: int, n: int)
{
  1 <= r <= n && 1 <= c <= n && 1 <= tr <= n && 1 <= tc <= n &&
  ((r == tr && c == tc)
   ||
   (var p := StepToward(r, c, tr, tc);
    ValidKingStep(r, c, p.0, p.1, n) &&
    ChebyshevDist(p.0, p.1, tr, tc) == ChebyshevDist(r, c, tr, tc) - 1))
}

// OPTIMALITY: no single king step can reduce Chebyshev distance by more than 1.
// By induction on path length, any path of k steps reduces distance by at most k,
// so the minimum number of moves from (r,c) to (tr,tc) is at least ChebyshevDist.
ghost predicate NoStepReducesByMoreThanOne(r: int, c: int, tr: int, tc: int)
{
  forall dr | -1 <= dr <= 1 ::
    forall dc | -1 <= dc <= 1 ::
      ChebyshevDist(r + dr, c + dc, tr, tc) >= ChebyshevDist(r, c, tr, tc) - 1
}

// Turn structure: White takes turns 1, 3, 5, … ; Black takes turns 2, 4, 6, …
// A king needing d optimal moves arrives at global turn:
//   2d−1 if White (moves first), or 2d if Black (moves second).
// If d = 0 the king starts on the coin (arrival turn 0).
ghost function ArrivalTurn(dist: int, movesFirst: bool): int
{
  if dist == 0 then 0
  else if movesFirst then 2 * dist - 1
  else 2 * dist
}

// The correct winner is the king whose arrival turn is strictly earlier.
ghost predicate CorrectWinner(winner: string, n: int, x: int, y: int)
  requires n >= 2 && 1 <= x <= n && 1 <= y <= n
{
  var whiteDist := ChebyshevDist(1, 1, x, y);
  var blackDist := ChebyshevDist(n, n, x, y);
  var whiteTurn := ArrivalTurn(whiteDist, true);
  var blackTurn := ArrivalTurn(blackDist, false);
  (winner == "White" <==> whiteTurn <= blackTurn) &&
  (winner == "Black" <==> whiteTurn > blackTurn)
}

// ── Method with specification ──

method KingsRace(n: int, x: int, y: int) returns (winner: string)
  requires n >= 2 && 1 <= x <= n && 1 <= y <= n
  ensures CorrectWinner(winner, n, x, y)
  ensures GreedyStepValid(1, 1, x, y, n)
  ensures GreedyStepValid(n, n, x, y, n)
  ensures NoStepReducesByMoreThanOne(1, 1, x, y)
  ensures NoStepReducesByMoreThanOne(n, n, x, y)
{
  var dx1 := if x - 1 >= 0 then x - 1 else 1 - x;
  var dy1 := if y - 1 >= 0 then y - 1 else 1 - y;
  var dist1 := if dx1 >= dy1 then dx1 else dy1;

  var dx2 := if x - n >= 0 then x - n else n - x;
  var dy2 := if y - n >= 0 then y - n else n - y;
  var dist2 := if dx2 >= dy2 then dx2 else dy2;

  if dist1 <= dist2 {
    winner := "White";
  } else {
    winner := "Black";
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0014_1075_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0014_1075_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0014_1075_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0014_1075_A/ (create the directory if needed).
