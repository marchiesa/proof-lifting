Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Find Square
Consider a table of size $$$n \times m$$$, initially fully white. Rows are numbered $$$1$$$ through $$$n$$$ from top to bottom, columns $$$1$$$ through $$$m$$$ from left to right. Some square inside the table with odd side length was painted black. Find the center of this square.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0003_1028_A/task.dfy

```dafny
ghost predicate ValidGrid(n: int, m: int, grid: seq<string>)
{
  n > 0 && m > 0 && |grid| == n &&
  (forall i | 0 <= i < n :: |grid[i]| == m) &&
  (forall i | 0 <= i < n :: forall j | 0 <= j < m ::
    grid[i][j] == 'W' || grid[i][j] == 'B')
}

// A cell (i,j) lies inside the axis-aligned square with given center and half-side-length
ghost predicate CellInSquare(i: int, j: int, centerRow: int, centerCol: int, half: int)
{
  centerRow - half <= i <= centerRow + half &&
  centerCol - half <= j <= centerCol + half
}

// The grid consists of exactly one black square of side length 2*half+1 (odd)
// centered at (centerRow, centerCol) in 0-indexed coordinates, with all other cells white
ghost predicate IsBlackSquareCenteredAt(n: int, m: int, grid: seq<string>,
                                   centerRow: int, centerCol: int, half: int)
  requires |grid| == n && n > 0 && m > 0
  requires forall i | 0 <= i < n :: |grid[i]| == m
{
  half >= 0 &&
  centerRow - half >= 0 && centerRow + half < n &&
  centerCol - half >= 0 && centerCol + half < m &&
  (forall i | 0 <= i < n ::
    forall j | 0 <= j < m ::
      if CellInSquare(i, j, centerRow, centerCol, half)
      then grid[i][j] == 'B'
      else grid[i][j] == 'W')
}

// There exists some black square painted on the grid
ghost predicate HasBlackSquare(n: int, m: int, grid: seq<string>)
  requires |grid| == n && n > 0 && m > 0
  requires forall i | 0 <= i < n :: |grid[i]| == m
{
  exists cr | 0 <= cr < n ::
    exists cc | 0 <= cc < m ::
      exists h: nat ::
        IsBlackSquareCenteredAt(n, m, grid, cr, cc, h)
}

method FindSquare(n: int, m: int, grid: seq<string>) returns (r: int, c: int)
  requires ValidGrid(n, m, grid)
  requires HasBlackSquare(n, m, grid)
  ensures 1 <= r <= n && 1 <= c <= m
  ensures exists h: nat ::
            IsBlackSquareCenteredAt(n, m, grid, r - 1, c - 1, h)
{
  var ly := 0;
  while ly < |grid| && 'B' !in grid[ly] {
    ly := ly + 1;
  }

  var ry := ly + 1;
  while ry < |grid| && 'B' in grid[ry] {
    ry := ry + 1;
  }

  var lx := 0;
  while lx < |grid[ly]| && grid[ly][lx] != 'B' {
    lx := lx + 1;
  }

  var rx := lx + 1;
  while rx < |grid[ly]| && grid[ly][rx] == 'B' {
    rx := rx + 1;
  }

  var y := (ly + ry) / 2;
  var x := (lx + rx) / 2;
  r := y + 1;
  c := x + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0003_1028_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0003_1028_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0003_1028_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0003_1028_A/ (create the directory if needed).
