// Count occurrences of a character in a single row
function CountCharInRow(row: seq<char>, ch: char): nat
  decreases |row|
{
  if |row| == 0 then 0
  else (if row[|row|-1] == ch then 1 else 0) + CountCharInRow(row[..|row|-1], ch)
}

// Count total occurrences of a character in the entire grid
function CountCharInGrid(grid: seq<seq<char>>, ch: char): nat
  decreases |grid|
{
  if |grid| == 0 then 0
  else CountCharInGrid(grid[..|grid|-1], ch) + CountCharInRow(grid[|grid|-1], ch)
}

// Check that grid is n x m (all rows have the same length m)
predicate IsRectangularGrid(grid: seq<seq<char>>, n: int, m: int)
{
  |grid| == n && n >= 0 && m >= 0 &&
  forall i | 0 <= i < n :: |grid[i]| == m
}

// Check that two grids have the same dimensions and only contain '.' and '*'
predicate ValidGridChars(grid: seq<seq<char>>, n: int, m: int)
  requires IsRectangularGrid(grid, n, m)
{
  forall i, j | 0 <= i < n && 0 <= j < m :: grid[i][j] == '.' || grid[i][j] == '*'
}

// The four positions form a rectangle with sides parallel to axes
predicate FourCornersFormRectangle(grid: seq<seq<char>>, n: int, m: int,
                                    r1: int, c1: int, r2: int, c2: int)
  requires IsRectangularGrid(grid, n, m)
{
  0 <= r1 < n && 0 <= r2 < n && 0 <= c1 < m && 0 <= c2 < m &&
  r1 != r2 && c1 != c2 &&
  grid[r1][c1] == '*' && grid[r1][c2] == '*' &&
  grid[r2][c1] == '*' && grid[r2][c2] == '*'
}

// Degenerate rectangle: two distinct rows, same column
predicate FourCornersFormDegenerateRowRect(grid: seq<seq<char>>, n: int, m: int,
                                            r1: int, r2: int, c1: int, c2: int)
  requires IsRectangularGrid(grid, n, m)
{
  0 <= r1 < n && 0 <= r2 < n && 0 <= c1 < m && 0 <= c2 < m &&
  r1 != r2 && c1 == c2 &&
  grid[r1][c1] == '*' && grid[r2][c1] == '*'
}

// Degenerate rectangle: same row, two distinct columns
predicate FourCornersFormDegenerateColRect(grid: seq<seq<char>>, n: int, m: int,
                                            r1: int, c1: int, r2: int, c2: int)
  requires IsRectangularGrid(grid, n, m)
{
  0 <= r1 < n && 0 <= r2 < n && 0 <= c1 < m && 0 <= c2 < m &&
  r1 == r2 && c1 != c2 &&
  grid[r1][c1] == '*' && grid[r1][c2] == '*'
}

// The marked cells in the output form an axis-aligned rectangle
predicate OutputFormsRectangle(result: seq<seq<char>>, n: int, m: int)
  requires IsRectangularGrid(result, n, m)
{
  exists r1, r2, c1, c2 | 0 <= r1 < n && 0 <= r2 < n && r1 < r2 &&
                            0 <= c1 < m && 0 <= c2 < m && c1 < c2 ::
    result[r1][c1] == '*' && result[r1][c2] == '*' &&
    result[r2][c1] == '*' && result[r2][c2] == '*' &&
    forall i, j | 0 <= i < n && 0 <= j < m ::
      (result[i][j] == '*') <==> ((i == r1 || i == r2) && (j == c1 || j == c2))
}

// The output preserves every star from the input
predicate PreservesOriginalStars(input: seq<seq<char>>, output: seq<seq<char>>, n: int, m: int)
  requires IsRectangularGrid(input, n, m)
  requires IsRectangularGrid(output, n, m)
{
  forall i, j | 0 <= i < n && 0 <= j < m ::
    (input[i][j] == '*') ==> (output[i][j] == '*')
}

// The output only differs from input by adding stars
predicate OnlyAddsStars(input: seq<seq<char>>, output: seq<seq<char>>, n: int, m: int)
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

method Main()
{
  // ========== SPEC POSITIVE TESTS ==========
  // All ensures predicates checked on correct input/output (small grids only)

  // Spec positive 2: 2x2, different row & col
  var inp: seq<seq<char>> := ["*.", ".*"];
  var out: seq<seq<char>> := ["**", "**"];
  expect IsRectangularGrid(out, 2, 2), "spec pos 2: IsRectangularGrid";
  expect PreservesOriginalStars(inp, out, 2, 2), "spec pos 2: PreservesOriginalStars";
  expect OnlyAddsStars(inp, out, 2, 2), "spec pos 2: OnlyAddsStars";
  expect CountCharInGrid(out, '*') == 4, "spec pos 2: CountCharInGrid";
  expect OutputFormsRectangle(out, 2, 2), "spec pos 2: OutputFormsRectangle";

  // Spec positive 3: 2x2, same column
  inp := ["*.", "*."];
  out := ["**", "**"];
  expect IsRectangularGrid(out, 2, 2), "spec pos 3: IsRectangularGrid";
  expect PreservesOriginalStars(inp, out, 2, 2), "spec pos 3: PreservesOriginalStars";
  expect OnlyAddsStars(inp, out, 2, 2), "spec pos 3: OnlyAddsStars";
  expect CountCharInGrid(out, '*') == 4, "spec pos 3: CountCharInGrid";
  expect OutputFormsRectangle(out, 2, 2), "spec pos 3: OutputFormsRectangle";

  // Spec positive 4: 3x3, opposite corners
  inp := ["*..", "...", "..*"];
  out := ["*.*", "...", "*.*"];
  expect IsRectangularGrid(out, 3, 3), "spec pos 4: IsRectangularGrid";
  expect PreservesOriginalStars(inp, out, 3, 3), "spec pos 4: PreservesOriginalStars";
  expect OnlyAddsStars(inp, out, 3, 3), "spec pos 4: OnlyAddsStars";
  expect CountCharInGrid(out, '*') == 4, "spec pos 4: CountCharInGrid";
  expect OutputFormsRectangle(out, 3, 3), "spec pos 4: OutputFormsRectangle";

  // Spec positive 5: 3x3, same column adjacent rows
  inp := [".*.", ".*.", "..."];
  out := ["**.", "**.", "..."];
  expect IsRectangularGrid(out, 3, 3), "spec pos 5: IsRectangularGrid";
  expect PreservesOriginalStars(inp, out, 3, 3), "spec pos 5: PreservesOriginalStars";
  expect OnlyAddsStars(inp, out, 3, 3), "spec pos 5: OnlyAddsStars";
  expect CountCharInGrid(out, '*') == 4, "spec pos 5: CountCharInGrid";
  expect OutputFormsRectangle(out, 3, 3), "spec pos 5: OutputFormsRectangle";

  // Spec positive 7: 2x2, same row
  inp := ["**", ".."];
  out := ["**", "**"];
  expect IsRectangularGrid(out, 2, 2), "spec pos 7: IsRectangularGrid";
  expect PreservesOriginalStars(inp, out, 2, 2), "spec pos 7: PreservesOriginalStars";
  expect OnlyAddsStars(inp, out, 2, 2), "spec pos 7: OnlyAddsStars";
  expect CountCharInGrid(out, '*') == 4, "spec pos 7: CountCharInGrid";
  expect OutputFormsRectangle(out, 2, 2), "spec pos 7: OutputFormsRectangle";

  // Spec positive 8: 3x3, same row middle
  inp := ["...", "*.*", "..."];
  out := ["*.*", "*.*", "..."];
  expect IsRectangularGrid(out, 3, 3), "spec pos 8: IsRectangularGrid";
  expect PreservesOriginalStars(inp, out, 3, 3), "spec pos 8: PreservesOriginalStars";
  expect OnlyAddsStars(inp, out, 3, 3), "spec pos 8: OnlyAddsStars";
  expect CountCharInGrid(out, '*') == 4, "spec pos 8: CountCharInGrid";
  expect OutputFormsRectangle(out, 3, 3), "spec pos 8: OutputFormsRectangle";

  // ========== SPEC NEGATIVE TESTS ==========
  // Wrong outputs (last row corrupted with " WRONG") must fail IsRectangularGrid

  // Spec negative 2: 2x2
  expect !IsRectangularGrid(["**", "** WRONG"], 2, 2), "spec neg 2";

  // Spec negative 3: 2x2
  expect !IsRectangularGrid(["**", "** WRONG"], 2, 2), "spec neg 3";

  // Spec negative 4: 3x3
  expect !IsRectangularGrid(["*.*", "...", "*.* WRONG"], 3, 3), "spec neg 4";

  // Spec negative 5: 3x3
  expect !IsRectangularGrid(["**.", "**.", "... WRONG"], 3, 3), "spec neg 5";

  // Spec negative 6: 4x4
  expect !IsRectangularGrid(["*..*", "....", "....", "*..* WRONG"], 4, 4), "spec neg 6";

  // Spec negative 7: 2x2
  expect !IsRectangularGrid(["**", "** WRONG"], 2, 2), "spec neg 7";

  // Spec negative 8: 3x3
  expect !IsRectangularGrid(["*.*", "*.*", "... WRONG"], 3, 3), "spec neg 8";

  // Spec negative 9: 5x5
  expect !IsRectangularGrid([".....", ".*.*.", ".....", ".*.*.", "..... WRONG"], 5, 5), "spec neg 9";

  // ========== IMPLEMENTATION TESTS ==========

  // Impl test 1a
  var r := AlmostRectangle(4, ["..*.", "....", "*...", "...."]);
  expect r == ["*.*.", "....", "*.*.", "...."], "impl test 1a failed";

  // Impl test 1b
  r := AlmostRectangle(2, ["*.", ".*"]);
  expect r == ["**", "**"], "impl test 1b failed";

  // Impl test 1c
  r := AlmostRectangle(2, [".*", ".*"]);
  expect r == ["**", "**"], "impl test 1c failed";

  // Impl test 1d
  r := AlmostRectangle(3, ["*.*", "...", "..."]);
  expect r == ["*.*", "*.*", "..."], "impl test 1d failed";

  // Impl test 1e
  r := AlmostRectangle(5, [".....", "..*..", ".....", ".*...", "....."]);
  expect r == [".....", ".**..", ".....", ".**..", "....."], "impl test 1e failed";

  // Impl test 1f
  r := AlmostRectangle(4, ["....", "....", "*...", "*..."]);
  expect r == ["....", "....", "**..", "**.."], "impl test 1f failed";

  // Impl test 2
  r := AlmostRectangle(2, ["*.", ".*"]);
  expect r == ["**", "**"], "impl test 2 failed";

  // Impl test 3
  r := AlmostRectangle(2, ["*.", "*."]);
  expect r == ["**", "**"], "impl test 3 failed";

  // Impl test 4
  r := AlmostRectangle(3, ["*..", "...", "..*"]);
  expect r == ["*.*", "...", "*.*"], "impl test 4 failed";

  // Impl test 5
  r := AlmostRectangle(3, [".*.", ".*.", "..."]);
  expect r == ["**.", "**.", "..."], "impl test 5 failed";

  // Impl test 6
  r := AlmostRectangle(4, ["*...", "....", "....", "...*"]);
  expect r == ["*..*", "....", "....", "*..*"], "impl test 6 failed";

  // Impl test 7
  r := AlmostRectangle(2, ["**", ".."]);
  expect r == ["**", "**"], "impl test 7 failed";

  // Impl test 8
  r := AlmostRectangle(3, ["...", "*.*", "..."]);
  expect r == ["*.*", "*.*", "..."], "impl test 8 failed";

  // Impl test 9
  r := AlmostRectangle(5, [".....", ".*...", ".....", "...*.", "....."]);
  expect r == [".....", ".*.*.", ".....", ".*.*.", "....."], "impl test 9 failed";

  // Impl test 10a
  r := AlmostRectangle(2, ["*.", ".*"]);
  expect r == ["**", "**"], "impl test 10a failed";

  // Impl test 10b
  r := AlmostRectangle(2, [".*", ".*"]);
  expect r == ["**", "**"], "impl test 10b failed";

  print "All tests passed\n";
}