predicate ValidGrid(n: int, m: int, grid: seq<string>)
{
  n > 0 && m > 0 && |grid| == n &&
  (forall i | 0 <= i < n :: |grid[i]| == m) &&
  (forall i | 0 <= i < n :: forall j | 0 <= j < m ::
    grid[i][j] == 'W' || grid[i][j] == 'B')
}

predicate CellInSquare(i: int, j: int, centerRow: int, centerCol: int, half: int)
{
  centerRow - half <= i <= centerRow + half &&
  centerCol - half <= j <= centerCol + half
}

predicate IsBlackSquareCenteredAt(n: int, m: int, grid: seq<string>,
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

predicate HasBlackSquare(n: int, m: int, grid: seq<string>)
  requires |grid| == n && n > 0 && m > 0
  requires forall i | 0 <= i < n :: |grid[i]| == m
{
  exists cr | 0 <= cr < n ::
    exists cc | 0 <= cc < m ::
      exists h | 0 <= h < n ::
        IsBlackSquareCenteredAt(n, m, grid, cr, cc, h)
}

// Wrapper for the ensures clause of FindSquare
predicate FindSquareEnsures(n: int, m: int, grid: seq<string>, r: int, c: int)
  requires |grid| == n && n > 0 && m > 0
  requires forall i | 0 <= i < n :: |grid[i]| == m
{
  1 <= r <= n && 1 <= c <= m &&
  exists h | 0 <= h < n ::
    IsBlackSquareCenteredAt(n, m, grid, r - 1, c - 1, h)
}

method FindSquare(n: int, m: int, grid: seq<string>) returns (r: int, c: int)
  requires ValidGrid(n, m, grid)
  requires HasBlackSquare(n, m, grid)
  ensures 1 <= r <= n && 1 <= c <= m
  ensures exists h | 0 <= h < n ::
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

method Main()
{
  var r: int, c: int;

  // ========== SPEC POSITIVE TESTS ==========
  // ensures predicate with correct outputs on small inputs

  expect FindSquareEnsures(3, 3, ["WWW", "BWW", "WWW"], 2, 1), "spec positive 1";
  expect FindSquareEnsures(3, 3, ["BBB", "BBB", "BBB"], 2, 2), "spec positive 2";
  expect FindSquareEnsures(3, 3, ["WBW", "WWW", "WWW"], 1, 2), "spec positive 3";
  expect FindSquareEnsures(3, 3, ["WWB", "WWW", "WWW"], 1, 3), "spec positive 4";
  expect FindSquareEnsures(3, 3, ["WWW", "WBW", "WWW"], 2, 2), "spec positive 5";
  expect FindSquareEnsures(3, 3, ["WWW", "WWB", "WWW"], 2, 3), "spec positive 6";
  expect FindSquareEnsures(3, 3, ["WWW", "WWW", "BWW"], 3, 1), "spec positive 7";
  expect FindSquareEnsures(3, 3, ["WWW", "WWW", "WBW"], 3, 2), "spec positive 8";
  expect FindSquareEnsures(1, 1, ["B"], 1, 1), "spec positive 9";
  expect FindSquareEnsures(3, 3, ["BWW", "WWW", "WWW"], 1, 1), "spec positive 10";

  // ========== SPEC NEGATIVE TESTS ==========
  // ensures predicate with WRONG outputs on small inputs

  expect !FindSquareEnsures(3, 3, ["WWW", "BWW", "WWW"], 3, 1), "spec negative 1";
  expect !FindSquareEnsures(3, 3, ["BBB", "BBB", "BBB"], 3, 2), "spec negative 2";
  expect !FindSquareEnsures(3, 3, ["WBW", "WWW", "WWW"], 2, 2), "spec negative 3";
  expect !FindSquareEnsures(3, 3, ["WWB", "WWW", "WWW"], 2, 3), "spec negative 4";
  expect !FindSquareEnsures(3, 3, ["WWW", "WBW", "WWW"], 3, 2), "spec negative 5";
  expect !FindSquareEnsures(3, 3, ["WWW", "WWB", "WWW"], 3, 3), "spec negative 6";
  expect !FindSquareEnsures(3, 3, ["WWW", "WWW", "BWW"], 4, 1), "spec negative 7";
  expect !FindSquareEnsures(3, 3, ["WWW", "WWW", "WBW"], 4, 2), "spec negative 8";

  // ========== IMPLEMENTATION TESTS ==========

  r, c := FindSquare(5, 6, ["WWBBBW", "WWBBBW", "WWBBBW", "WWWWWW", "WWWWWW"]);
  expect r == 2 && c == 4, "impl test 1 failed";

  r, c := FindSquare(3, 3, ["WWW", "BWW", "WWW"]);
  expect r == 2 && c == 1, "impl test 2 failed";

  r, c := FindSquare(5, 5, ["WWWWW", "WBBBW", "WBBBW", "WBBBW", "WWWWW"]);
  expect r == 3 && c == 3, "impl test 3 failed";

  r, c := FindSquare(3, 3, ["BBB", "BBB", "BBB"]);
  expect r == 2 && c == 2, "impl test 4 failed";

  r, c := FindSquare(3, 3, ["WBW", "WWW", "WWW"]);
  expect r == 1 && c == 2, "impl test 5 failed";

  r, c := FindSquare(3, 3, ["WWB", "WWW", "WWW"]);
  expect r == 1 && c == 3, "impl test 6 failed";

  r, c := FindSquare(3, 3, ["WWW", "WBW", "WWW"]);
  expect r == 2 && c == 2, "impl test 7 failed";

  r, c := FindSquare(3, 3, ["WWW", "WWB", "WWW"]);
  expect r == 2 && c == 3, "impl test 8 failed";

  r, c := FindSquare(3, 3, ["WWW", "WWW", "BWW"]);
  expect r == 3 && c == 1, "impl test 9 failed";

  r, c := FindSquare(3, 3, ["WWW", "WWW", "WBW"]);
  expect r == 3 && c == 2, "impl test 10 failed";

  r, c := FindSquare(3, 3, ["WWW", "WWW", "WWB"]);
  expect r == 3 && c == 3, "impl test 11 failed";

  r, c := FindSquare(1, 89, ["WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWBWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW"]);
  expect r == 1 && c == 45, "impl test 12 failed";

  r, c := FindSquare(96, 1, [
    "W","W","W","W","W","W","W","W","W","W",
    "W","W","W","W","W","W","W","W","W","W",
    "W","W","W","W","W","W","W","W","W","W",
    "W","W","W","W","W","W","W","W","W","W",
    "W","W","W","W","W","W","W","W","W","W",
    "W","W","W","W","W","W","W","W","W","W",
    "W","W","W","W","W","W","W","W","W","W",
    "W","W","W","W","W","W","W","W","W","W",
    "W","W","W","W","W","W","W","W","B","W",
    "W","W","W","W","W","W"
  ]);
  expect r == 89 && c == 1, "impl test 13 failed";

  r, c := FindSquare(1, 1, ["B"]);
  expect r == 1 && c == 1, "impl test 14 failed";

  r, c := FindSquare(3, 3, ["BWW", "WWW", "WWW"]);
  expect r == 1 && c == 1, "impl test 15 failed";

  r, c := FindSquare(2, 3, ["WWB", "WWW"]);
  expect r == 1 && c == 3, "impl test 16 failed";

  r, c := FindSquare(3, 5, ["WWWWW", "WWWWW", "WWWWB"]);
  expect r == 3 && c == 5, "impl test 17 failed";

  r, c := FindSquare(1, 5, ["WWWWB"]);
  expect r == 1 && c == 5, "impl test 18 failed";

  r, c := FindSquare(7, 7, ["BBBBBWW", "BBBBBWW", "BBBBBWW", "BBBBBWW", "BBBBBWW", "WWWWWWW", "WWWWWWW"]);
  expect r == 3 && c == 3, "impl test 19 failed";

  r, c := FindSquare(3, 4, ["WBBB", "WBBB", "WBBB"]);
  expect r == 2 && c == 3, "impl test 20 failed";

  print "All tests passed\n";
}