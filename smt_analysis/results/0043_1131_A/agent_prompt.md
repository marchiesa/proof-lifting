Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Sea Battle
In order to make the "Sea Battle" game more interesting, Boris decided to add a new ship type to it. The ship consists of two rectangles. The first rectangle has a width of $$$w_1$$$ and a height of $$$h_1$$$, while the second rectangle has a width of $$$w_2$$$ and a height of $$$h_2$$$, where $$$w_1 \ge w_2$$$. In this game, exactly one ship is used, made up of two rectangles. There are no other ships on the field.

The rectangles are placed on field in the following way:

- the second rectangle is on top the first rectangle;
- they are aligned to the left, i.e. their left sides are on the same line;
- the rectangles are adjacent to each other without a gap.

See the pictures in the notes: the first rectangle is colored red, the second rectangle is colored blue.

Formally, let's introduce a coordinate system. Then, the leftmost bottom cell of the first rectangle has coordinates $$$(1, 1)$$$, the rightmost top cell of the first rectangle has coordinates $$$(w_1, h_1)$$$, the leftmost bottom cell of the second rectangle has coordinates $$$(1, h_1 + 1)$$$ and the rightmost top cell of the second rectangle has coordinates $$$(w_2, h_1 + h_2)$$$.

After the ship is completely destroyed, all cells neighboring by side or a corner with the ship are marked. Of course, only cells, which don't belong to the ship are marked. On the pictures in the notes such cells are colored green.

Find out how many cells should be marked after the ship is destroyed. The field of the game is infinite in any direction.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0043_1131_A/task.dfy

```dafny
// The ship consists of two left-aligned rectangles stacked vertically.
// Bottom rectangle: cells (x, y) with 1 <= x <= w1, 1 <= y <= h1
// Top rectangle:    cells (x, y) with 1 <= x <= w2, h1+1 <= y <= h1+h2
ghost predicate IsShipCell(x: int, y: int, w1: int, h1: int, w2: int, h2: int)
{
  (1 <= x <= w1 && 1 <= y <= h1) ||
  (1 <= x <= w2 && h1 + 1 <= y <= h1 + h2)
}

// A cell is marked if it is NOT part of the ship but is adjacent
// (by side or corner, i.e., Chebyshev distance 1) to at least one ship cell.
ghost predicate IsMarkedCell(x: int, y: int, w1: int, h1: int, w2: int, h2: int)
{
  !IsShipCell(x, y, w1, h1, w2, h2) &&
  exists dx | -1 <= dx <= 1 ::
    exists dy | -1 <= dy <= 1 ::
      !(dx == 0 && dy == 0) && IsShipCell(x + dx, y + dy, w1, h1, w2, h2)
}

// Count marked cells in row y for x in [x..xHi]
ghost function CountMarkedRow(x: int, xHi: int, y: int,
                        w1: int, h1: int, w2: int, h2: int): int
  decreases xHi - x + 1
{
  if x > xHi then 0
  else (if IsMarkedCell(x, y, w1, h1, w2, h2) then 1 else 0)
       + CountMarkedRow(x + 1, xHi, y, w1, h1, w2, h2)
}

// Count marked cells in grid for y in [y..yHi], x in [xLo..xHi]
ghost function CountMarkedGrid(y: int, yHi: int, xLo: int, xHi: int,
                         w1: int, h1: int, w2: int, h2: int): int
  decreases yHi - y + 1
{
  if y > yHi then 0
  else CountMarkedRow(xLo, xHi, y, w1, h1, w2, h2)
       + CountMarkedGrid(y + 1, yHi, xLo, xHi, w1, h1, w2, h2)
}

// All marked cells lie within the bounding box [0, w1+1] x [0, h1+h2+1].
ghost function TotalMarked(w1: int, h1: int, w2: int, h2: int): int
  requires w1 >= 1 && h1 >= 1 && w2 >= 1 && h2 >= 1 && w1 >= w2
{
  CountMarkedGrid(0, h1 + h2 + 1, 0, w1 + 1, w1, h1, w2, h2)
}

method SeaBattle(w1: int, h1: int, w2: int, h2: int) returns (marked: int)
  requires w1 >= 1 && h1 >= 1 && w2 >= 1 && h2 >= 1 && w1 >= w2
  ensures marked == TotalMarked(w1, h1, w2, h2)
{
  marked := (w1 + 2) * (h1 + h2 + 2) - (w1 - w2) * h2 - w1 * h1 - w2 * h2;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0043_1131_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0043_1131_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0043_1131_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0043_1131_A/ (create the directory if needed).
