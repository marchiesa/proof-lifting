Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Almost Rectangle
There is a square field of size $$$n \times n$$$ in which two cells are marked. These cells can be in the same row or column.

You are to mark two more cells so that they are the corners of a rectangle with sides parallel to the coordinate axes.

For example, if $$$n=4$$$ and a rectangular field looks like this (there are asterisks in the marked cells):

$$$$$$ \begin{matrix} . & . & * & . \\ . & . & . & . \\ * & . & . & . \\ . & . & . & . \\ \end{matrix} $$$$$$

Then you can mark two more cells as follows

$$$$$$ \begin{matrix} * & . & * & . \\ . & . & . & . \\ * & . & * & . \\ . & . & . & . \\ \end{matrix} $$$$$$

If there are several possible solutions, then print any of them.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0216_1512_B/task.dfy

```dafny
// Count occurrences of a character in a single row
ghost function CountCharInRow(row: seq<char>, ch: char): nat
  decreases |row|
{
  if |row| == 0 then 0
  else (if row[|row|-1] == ch then 1 else 0) + CountCharInRow(row[..|row|-1], ch)
}

// Count total occurrences of a character in the entire grid
ghost function CountCharInGrid(grid: seq<seq<char>>, ch: char): nat
  decreases |grid|
{
  if |grid| == 0 then 0
  else CountCharInGrid(grid[..|grid|-1], ch) + CountCharInRow(grid[|grid|-1], ch)
}

// Check that grid is n x m (all rows have the same length m)
ghost predicate IsRectangularGrid(grid: seq<seq<char>>, n: int, m: int)
{
  |grid| == n && n >= 0 && m >= 0 &&
  forall i | 0 <= i < n :: |grid[i]| == m
}

// Check that two grids have the same dimensions and only contain '.' and '*'
ghost predicate ValidGridChars(grid: seq<seq<char>>, n: int, m: int)
  requires IsRectangularGrid(grid, n, m)
{
  forall i, j | 0 <= i < n && 0 <= j < m :: grid[i][j] == '.' || grid[i][j] == '*'
}

// The four positions (r1,c1), (r1,c2), (r2,c1), (r2,c2) form a rectangle with
// sides parallel to axes, where r1 != r2 and c1 != c2
ghost predicate FourCornersFormRectangle(grid: seq<seq<char>>, n: int, m: int,
                                    r1: int, c1: int, r2: int, c2: int)
  requires IsRectangularGrid(grid, n, m)
{
  0 <= r1 < n && 0 <= r2 < n && 0 <= c1 < m && 0 <= c2 < m &&
  r1 != r2 && c1 != c2 &&
  grid[r1][c1] == '*' && grid[r1][c2] == '*' &&
  grid[r2][c1] == '*' && grid[r2][c2] == '*'
}

// Degenerate rectangle: all 4 stars in the same row (r1 == r2), two distinct columns
ghost predicate FourCornersFormDegenerateRowRect(grid: seq<seq<char>>, n: int, m: int,
                                            r1: int, r2: int, c1: int, c2: int)
  requires IsRectangularGrid(grid, n, m)
{
  0 <= r1 < n && 0 <= r2 < n && 0 <= c1 < m && 0 <= c2 < m &&
  r1 != r2 && c1 == c2 &&
  grid[r1][c1] == '*' && grid[r2][c1] == '*'
}

// Degenerate rectangle: all 4 stars in the same column (c1 == c2), two distinct rows
ghost predicate FourCornersFormDegenerateColRect(grid: seq<seq<char>>, n: int, m: int,
                                            r1: int, c1: int, r2: int, c2: int)
  requires IsRectangularGrid(grid, n, m)
{
  0 <= r1 < n && 0 <= r2 < n && 0 <= c1 < m && 0 <= c2 < m &&
  r1 == r2 && c1 != c2 &&
  grid[r1][c1] == '*' && grid[r1][c2] == '*'
}

// The marked cells in the output form an axis-aligned rectangle.
// This covers 3 cases based on the input stars' positions:
//   - Different rows and different columns: a proper 4-corner rectangle
//   - Same row: pick another row, forming a rectangle with 2 distinct rows and 2 distinct columns
//   - Same column: pick another column, forming a rectangle with 2 distinct rows and 2 distinct columns
// In ALL cases, exactly 4 stars exist and they sit at 4 corners of a rectangle (rows x cols).
ghost predicate OutputFormsRectangle(result: seq<seq<char>>, n: int, m: int)
  requires IsRectangularGrid(result, n, m)
{
  exists r1, r2, c1, c2 | 0 <= r1 < n && 0 <= r2 < n && r1 < r2 &&
                            0 <= c1 < m && 0 <= c2 < m && c1 < c2 ::
    result[r1][c1] == '*' && result[r1][c2] == '*' &&
    result[r2][c1] == '*' && result[r2][c2] == '*' &&
    // These 4 corners account for ALL stars in the grid
    forall i, j | 0 <= i < n && 0 <= j < m ::
      (result[i][j] == '*') <==> ((i == r1 || i == r2) && (j == c1 || j == c2))
}

// The output preserves every star from the input (original stars are kept)
ghost predicate PreservesOriginalStars(input: seq<seq<char>>, output: seq<seq<char>>, n: int, m: int)
  requires IsRectangularGrid(input, n, m)
  requires IsRectangularGrid(output, n, m)
{
  forall i, j | 0 <= i < n && 0 <= j < m ::
    (input[i][j] == '*') ==> (output[i][j] == '*')
}

// The output only differs from input by adding stars (never removes or changes non-star cells to something else)
ghost predicate OnlyAddsStars(input: seq<seq<char>>, output: seq<seq<char>>, n: int, m: int)
  requires IsRectangularGrid(input, n, m)
  requires IsRectangularGrid(output, n, m)
{
  forall i, j | 0 <= i < n && 0 <= j < m ::
    (output[i][j] != input[i][j]) ==> (input[i][j] == '.' && output[i][j] == '*')
}

method AlmostRectangle(n: int, grid: seq<seq<char>>) returns (result: seq<seq<char>>)
  requires n >= 2
  requires IsRectangularGrid(grid, n, |grid[0]|)
  requires |grid[0]| >= 2
  requires ValidGridChars(grid, n, |grid[0]|)
  requires CountCharInGrid(grid, '*') == 2
  ensures IsRectangularGrid(result, n, |grid[0]|)
  ensures PreservesOriginalStars(grid, result, n, |grid[0]|)
  ensures OnlyAddsStars(grid, result, n, |grid[0]|)
  ensures CountCharInGrid(result, '*') == 4
  ensures OutputFormsRectangle(result, n, |grid[0]|)
{
  var res := new seq<char>[n];
  var i := 0;
  while i < n {
    res[i] := grid[i];
    i := i + 1;
  }

  var a := -1;
  var c := -1;
  var b := -1;
  var d := -1;
  i := 0;
  while i < n {
    var j := 0;
    while j < |res[i]| {
      if res[i][j] == '*' {
        if a == -1 {
          a := i;
          c := j;
        } else {
          b := i;
          d := j;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }

  if a != b && c != d {
    res[a] := res[a][d := '*'];
    res[b] := res[b][c := '*'];
  } else if a == b {
    var nr := 0;
    if nr == a {
      nr := 1;
    }
    res[nr] := res[nr][c := '*'];
    res[nr] := res[nr][d := '*'];
  } else {
    var nc := 0;
    if nc == c {
      nc := 1;
    }
    res[a] := res[a][nc := '*'];
    res[b] := res[b][nc := '*'];
  }

  result := [];
  i := 0;
  while i < n {
    result := result + [res[i]];
    i := i + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0216_1512_B/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0216_1512_B/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0216_1512_B/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0216_1512_B/ (create the directory if needed).
