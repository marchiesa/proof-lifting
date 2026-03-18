method FindSquare(n: int, m: int, grid: seq<string>) returns (r: int, c: int)
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

  // Test 1
  r, c := FindSquare(5, 6, ["WWBBBW", "WWBBBW", "WWBBBW", "WWWWWW", "WWWWWW"]);
  expect r == 2 && c == 4, "Test 1 failed";

  // Test 2
  r, c := FindSquare(3, 3, ["WWW", "BWW", "WWW"]);
  expect r == 2 && c == 1, "Test 2 failed";

  // Test 3
  r, c := FindSquare(5, 5, ["WWWWW", "WBBBW", "WBBBW", "WBBBW", "WWWWW"]);
  expect r == 3 && c == 3, "Test 3 failed";

  // Test 4
  r, c := FindSquare(3, 3, ["BBB", "BBB", "BBB"]);
  expect r == 2 && c == 2, "Test 4 failed";

  // Test 5
  r, c := FindSquare(3, 3, ["WBW", "WWW", "WWW"]);
  expect r == 1 && c == 2, "Test 5 failed";

  // Test 6
  r, c := FindSquare(3, 3, ["WWB", "WWW", "WWW"]);
  expect r == 1 && c == 3, "Test 6 failed";

  // Test 7
  r, c := FindSquare(3, 3, ["WWW", "WBW", "WWW"]);
  expect r == 2 && c == 2, "Test 7 failed";

  // Test 8
  r, c := FindSquare(3, 3, ["WWW", "WWB", "WWW"]);
  expect r == 2 && c == 3, "Test 8 failed";

  // Test 9
  r, c := FindSquare(3, 3, ["WWW", "WWW", "BWW"]);
  expect r == 3 && c == 1, "Test 9 failed";

  // Test 10
  r, c := FindSquare(3, 3, ["WWW", "WWW", "WBW"]);
  expect r == 3 && c == 2, "Test 10 failed";

  // Test 11
  r, c := FindSquare(3, 3, ["WWW", "WWW", "WWB"]);
  expect r == 3 && c == 3, "Test 11 failed";

  // Test 12
  r, c := FindSquare(1, 89, ["WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWBWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW"]);
  expect r == 1 && c == 45, "Test 12 failed";

  // Test 13
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
  expect r == 89 && c == 1, "Test 13 failed";

  // Test 14
  r, c := FindSquare(1, 1, ["B"]);
  expect r == 1 && c == 1, "Test 14 failed";

  // Test 15
  r, c := FindSquare(3, 3, ["BWW", "WWW", "WWW"]);
  expect r == 1 && c == 1, "Test 15 failed";

  // Test 16
  r, c := FindSquare(2, 3, ["WWB", "WWW"]);
  expect r == 1 && c == 3, "Test 16 failed";

  // Test 17
  r, c := FindSquare(3, 5, ["WWWWW", "WWWWW", "WWWWB"]);
  expect r == 3 && c == 5, "Test 17 failed";

  // Test 18
  r, c := FindSquare(1, 5, ["WWWWB"]);
  expect r == 1 && c == 5, "Test 18 failed";

  // Test 19
  r, c := FindSquare(7, 7, ["BBBBBWW", "BBBBBWW", "BBBBBWW", "BBBBBWW", "BBBBBWW", "WWWWWWW", "WWWWWWW"]);
  expect r == 3 && c == 3, "Test 19 failed";

  // Test 20
  r, c := FindSquare(3, 4, ["WBBB", "WBBB", "WBBB"]);
  expect r == 2 && c == 3, "Test 20 failed";

  print "All tests passed\n";
}