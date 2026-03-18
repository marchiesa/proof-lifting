// ===== SPEC PREDICATES AND FUNCTIONS =====

predicate IsGrid(a: seq<seq<int>>, n: int, m: int)
{
  |a| == n && n >= 3 && m >= 3 &&
  forall i | 0 <= i < n :: |a[i]| == m &&
    forall j | 0 <= j < m :: a[i][j] == 0 || a[i][j] == 1
}

predicate PlatesOnEdge(a: seq<seq<int>>, n: int, m: int)
  requires IsGrid(a, n, m)
{
  forall i, j | 0 <= i < n && 0 <= j < m ::
    a[i][j] == 1 ==> (i == 0 || i == n - 1 || j == 0 || j == m - 1)
}

predicate NoAdjacentPlates(a: seq<seq<int>>, n: int, m: int)
  requires IsGrid(a, n, m)
{
  forall i1, j1, i2, j2 |
    0 <= i1 < n && 0 <= j1 < m &&
    0 <= i2 < n && 0 <= j2 < m &&
    (i1, j1) != (i2, j2) &&
    -1 <= i1 - i2 <= 1 && -1 <= j1 - j2 <= 1 ::
    !(a[i1][j1] == 1 && a[i2][j2] == 1)
}

predicate ValidPlacement(a: seq<seq<int>>, n: int, m: int)
  requires IsGrid(a, n, m)
{
  PlatesOnEdge(a, n, m) && NoAdjacentPlates(a, n, m)
}

function CountRow(row: seq<int>): int
  decreases |row|
{
  if |row| == 0 then 0
  else CountRow(row[..|row| - 1]) + row[|row| - 1]
}

function CountPlates(a: seq<seq<int>>): int
  decreases |a|
{
  if |a| == 0 then 0
  else CountPlates(a[..|a| - 1]) + CountRow(a[|a| - 1])
}

function BuildRow(bits: seq<int>, m: int, offset: int): seq<int>
  requires offset >= 0
  requires offset + m <= |bits|
  decreases m
{
  if m == 0 then []
  else [bits[offset]] + BuildRow(bits, m - 1, offset + 1)
}

function BuildGrid(bits: seq<int>, n: int, m: int, row: int): seq<seq<int>>
  requires n >= 0 && m >= 0 && row >= 0
  requires row <= n
  requires |bits| == n * m
  decreases n - row
{
  if row == n then []
  else [BuildRow(bits, m, row * m)] + BuildGrid(bits, n, m, row + 1)
}

predicate AllBinary(bits: seq<int>)
{
  forall i | 0 <= i < |bits| :: bits[i] == 0 || bits[i] == 1
}

predicate ValidPlacementFromBits(bits: seq<int>, n: int, m: int, count: int)
  requires n >= 3 && m >= 3
  requires |bits| == n * m
  requires AllBinary(bits)
{
  var g := BuildGrid(bits, n, m, 0);
  IsGrid(g, n, m) && ValidPlacement(g, n, m) && CountPlates(g) == count
}

predicate IsOptimal(a: seq<seq<int>>, n: int, m: int)
  requires IsGrid(a, n, m)
  requires ValidPlacement(a, n, m)
{
  var count := CountPlates(a);
  forall bits: seq<int> | |bits| == n * m && AllBinary(bits) ::
    var g := BuildGrid(bits, n, m, 0);
    (IsGrid(g, n, m) && ValidPlacement(g, n, m)) ==> CountPlates(g) <= count
}

// ===== IMPLEMENTATION =====

method Solve(n: int, m: int, r: int, c: int) returns (a: seq<seq<int>>, ans: int)
  requires n >= 3 && m >= 3
  requires 0 <= r < n && 0 <= c < m
  ensures IsGrid(a, n, m)
  ensures ValidPlacement(a, n, m)
  ensures ans == CountPlates(a)
{
  a := [];
  var idx := 0;
  while idx < n
  {
    var row: seq<int> := [];
    var jdx := 0;
    while jdx < m
    {
      row := row + [0];
      jdx := jdx + 1;
    }
    a := a + [row];
    idx := idx + 1;
  }

  a := a[r := a[r][c := 1]];

  var i := 0;
  while i < m
  {
    if !(a[0][i] == 1 || (i > 0 && a[0][i - 1] == 1) || (i + 1 < m && a[0][i + 1] == 1)) {
      a := a[0 := a[0][i := 1]];
    }
    i := i + 1;
  }

  i := 1;
  while i < n
  {
    if !(a[i][m - 1] == 1 || (i > 0 && a[i - 1][m - 1] == 1) || (i > 0 && a[i - 1][m - 2] == 1)) {
      a := a[i := a[i][m - 1 := 1]];
    }
    i := i + 1;
  }

  i := m - 2;
  while i >= 0
  {
    if !(a[n - 1][i] == 1 || (i > 0 && a[n - 1][i - 1] == 1) || (i + 1 < m && a[n - 1][i + 1] == 1) || (i + 1 < m && a[n - 2][i + 1] == 1)) {
      a := a[n - 1 := a[n - 1][i := 1]];
    }
    i := i - 1;
  }

  i := n - 2;
  while i >= 1
  {
    if !(a[i][0] == 1 || (i > 0 && a[i - 1][0] == 1) || (i > 0 && a[i - 1][1] == 1) || (i < n - 1 && a[i + 1][0] == 1) || (i < n - 1 && a[i + 1][1] == 1)) {
      a := a[i := a[i][0 := 1]];
    }
    i := i - 1;
  }

  ans := 0;
  i := 0;
  while i < n
  {
    var j := 0;
    while j < m
    {
      ans := ans + a[i][j];
      j := j + 1;
    }
    i := i + 1;
  }
}

method PuttingPlates(h: int, w: int) returns (grid: seq<seq<int>>)
  requires h >= 3 && w >= 3
  ensures IsGrid(grid, h, w)
  ensures ValidPlacement(grid, h, w)
  ensures IsOptimal(grid, h, w)
{
  var a1, ans1 := Solve(h, w, 0, 0);
  var a2, ans2 := Solve(h, w, 0, 1);
  if ans1 > ans2 {
    grid := a1;
  } else {
    grid := a2;
  }
}

// ===== TEST HELPERS =====

method ParseGrid(rows: seq<string>) returns (grid: seq<seq<int>>)
{
  grid := [];
  var i := 0;
  while i < |rows|
  {
    var row: seq<int> := [];
    var j := 0;
    while j < |rows[i]|
    {
      if rows[i][j] == '1' {
        row := row + [1];
      } else {
        row := row + [0];
      }
      j := j + 1;
    }
    grid := grid + [row];
    i := i + 1;
  }
}

method ParseGridRaw(rows: seq<string>) returns (grid: seq<seq<int>>)
{
  grid := [];
  var i := 0;
  while i < |rows|
  {
    var row: seq<int> := [];
    var j := 0;
    while j < |rows[i]|
    {
      var c := rows[i][j];
      if c == '0' {
        row := row + [0];
      } else if c == '1' {
        row := row + [1];
      } else if c == '2' {
        row := row + [2];
      } else {
        row := row + [0];
      }
      j := j + 1;
    }
    grid := grid + [row];
    i := i + 1;
  }
}

method CheckImpl(h: int, w: int, expectedRows: seq<string>, name: string)
  requires h >= 3 && w >= 3
{
  var result := PuttingPlates(h, w);
  var expected := ParseGrid(expectedRows);
  expect result == expected, name;
}

method Main()
{
  var g: seq<seq<int>>;

  // ===== SPEC POSITIVE TESTS =====
  // Test IsGrid and ValidPlacement on correct outputs (small grids only)

  // spec positive 1: 3x3
  g := ParseGrid(["101","000","101"]);
  expect IsGrid(g, 3, 3), "spec positive 1: IsGrid (3x3)";
  expect ValidPlacement(g, 3, 3), "spec positive 1: ValidPlacement (3x3)";

  // spec positive 2: 3x4
  g := ParseGrid(["0101","0000","0101"]);
  expect IsGrid(g, 3, 4), "spec positive 2: IsGrid (3x4)";
  expect ValidPlacement(g, 3, 4), "spec positive 2: ValidPlacement (3x4)";

  // spec positive 3: 4x3
  g := ParseGrid(["101","000","001","100"]);
  expect IsGrid(g, 4, 3), "spec positive 3: IsGrid (4x3)";
  expect ValidPlacement(g, 4, 3), "spec positive 3: ValidPlacement (4x3)";

  // spec positive 4: 3x5
  g := ParseGrid(["10101","00000","10101"]);
  expect IsGrid(g, 3, 5), "spec positive 4: IsGrid (3x5)";
  expect ValidPlacement(g, 3, 5), "spec positive 4: ValidPlacement (3x5)";

  // spec positive 5: 4x4
  g := ParseGrid(["0101","0000","0001","0100"]);
  expect IsGrid(g, 4, 4), "spec positive 5: IsGrid (4x4)";
  expect ValidPlacement(g, 4, 4), "spec positive 5: ValidPlacement (4x4)";

  // spec positive 6: 5x5
  g := ParseGrid(["10101","00000","10001","00000","10101"]);
  expect IsGrid(g, 5, 5), "spec positive 6: IsGrid (5x5)";
  expect ValidPlacement(g, 5, 5), "spec positive 6: ValidPlacement (5x5)";

  // spec positive 7: 5x6
  g := ParseGrid(["010101","000000","100001","000000","010101"]);
  expect IsGrid(g, 5, 6), "spec positive 7: IsGrid (5x6)";
  expect ValidPlacement(g, 5, 6), "spec positive 7: ValidPlacement (5x6)";

  // spec positive 8: 4x5
  g := ParseGrid(["10101","00000","00001","10100"]);
  expect IsGrid(g, 4, 5), "spec positive 8: IsGrid (4x5)";
  expect ValidPlacement(g, 4, 5), "spec positive 8: ValidPlacement (4x5)";

  // spec positive 9: 6x5
  g := ParseGrid(["10101","00000","00001","10000","00001","10100"]);
  expect IsGrid(g, 6, 5), "spec positive 9: IsGrid (6x5)";
  expect ValidPlacement(g, 6, 5), "spec positive 9: ValidPlacement (6x5)";

  // spec positive 10: 6x6
  g := ParseGrid(["010101","000000","000001","100000","000001","010100"]);
  expect IsGrid(g, 6, 6), "spec positive 10: IsGrid (6x6)";
  expect ValidPlacement(g, 6, 6), "spec positive 10: ValidPlacement (6x6)";

  // ===== SPEC NEGATIVE TESTS =====
  // Test that wrong outputs (containing '2') fail IsGrid

  // spec negative 1: 3x3 wrong (last char of row 0: '1'->'2')
  g := ParseGridRaw(["102","000","101"]);
  expect !IsGrid(g, 3, 3), "spec negative 1 (3x3)";

  // spec negative 2: 3x4 wrong (row 0 is "102" — wrong length and has 2)
  g := ParseGridRaw(["102","0000","0101"]);
  expect !IsGrid(g, 3, 4), "spec negative 2 (3x4)";

  // spec negative 3: 4x3 wrong (row 0 has '2')
  g := ParseGridRaw(["102","000","001","100"]);
  expect !IsGrid(g, 4, 3), "spec negative 3 (4x3)";

  // spec negative 4: 3x5 wrong (last char of row 0: '1'->'2')
  g := ParseGridRaw(["10102","00000","10101"]);
  expect !IsGrid(g, 3, 5), "spec negative 4 (3x5)";

  // spec negative 5: 4x4 wrong (row 0 is "102" — wrong length)
  g := ParseGridRaw(["102","0000","0001","0100"]);
  expect !IsGrid(g, 4, 4), "spec negative 5 (4x4)";

  // spec negative 6: 5x5 wrong (last char of row 0: '1'->'2')
  g := ParseGridRaw(["10102","00000","10001","00000","10101"]);
  expect !IsGrid(g, 5, 5), "spec negative 6 (5x5)";

  // spec negative 7: 5x6 wrong (row 0 is "10102" — wrong length and has 2)
  g := ParseGridRaw(["10102","000000","100001","000000","010101"]);
  expect !IsGrid(g, 5, 6), "spec negative 7 (5x6)";

  // spec negative 8: 6x5 wrong — extra negative from Neg 4 (6x5 not present but
  // we can test Neg 1 first subcase: 3x5 with "10102")
  // Already covered above. Use 6x6 wrong from Neg 4 second subcase instead:
  // Neg 9 (5x6 already done). Let's add 3x20 wrong:
  g := ParseGridRaw(["1010101010101010102","00000000000000000000","01010101010101010101"]);
  expect !IsGrid(g, 3, 20), "spec negative 8 (3x20)";

  // ===== IMPLEMENTATION TESTS =====

  CheckImpl(3, 3, [
    "101",
    "000",
    "101"
  ], "impl test 1 (3x3)");

  CheckImpl(3, 4, [
    "0101",
    "0000",
    "0101"
  ], "impl test 2 (3x4)");

  CheckImpl(3, 5, [
    "10101",
    "00000",
    "10101"
  ], "impl test 3 (3x5)");

  CheckImpl(3, 20, [
    "01010101010101010101",
    "00000000000000000000",
    "01010101010101010101"
  ], "impl test 4 (3x20)");

  CheckImpl(4, 3, [
    "101",
    "000",
    "001",
    "100"
  ], "impl test 5 (4x3)");

  CheckImpl(4, 4, [
    "0101",
    "0000",
    "0001",
    "0100"
  ], "impl test 6 (4x4)");

  CheckImpl(4, 5, [
    "10101",
    "00000",
    "00001",
    "10100"
  ], "impl test 7 (4x5)");

  CheckImpl(4, 20, [
    "01010101010101010101",
    "00000000000000000000",
    "00000000000000000001",
    "01010101010101010100"
  ], "impl test 8 (4x20)");

  CheckImpl(5, 5, [
    "10101",
    "00000",
    "10001",
    "00000",
    "10101"
  ], "impl test 9 (5x5)");

  CheckImpl(5, 6, [
    "010101",
    "000000",
    "100001",
    "000000",
    "010101"
  ], "impl test 10 (5x6)");

  CheckImpl(5, 18, [
    "010101010101010101",
    "000000000000000000",
    "100000000000000001",
    "000000000000000000",
    "010101010101010101"
  ], "impl test 11 (5x18)");

  CheckImpl(6, 5, [
    "10101",
    "00000",
    "00001",
    "10000",
    "00001",
    "10100"
  ], "impl test 12 (6x5)");

  CheckImpl(6, 6, [
    "010101",
    "000000",
    "000001",
    "100000",
    "000001",
    "010100"
  ], "impl test 13 (6x6)");

  CheckImpl(6, 7, [
    "1010101",
    "0000000",
    "0000001",
    "1000000",
    "0000001",
    "1010100"
  ], "impl test 14 (6x7)");

  CheckImpl(7, 19, [
    "1010101010101010101",
    "0000000000000000000",
    "1000000000000000001",
    "0000000000000000000",
    "1000000000000000001",
    "0000000000000000000",
    "1010101010101010101"
  ], "impl test 15 (7x19)");

  CheckImpl(9, 14, [
    "01010101010101",
    "00000000000000",
    "10000000000001",
    "00000000000000",
    "10000000000001",
    "00000000000000",
    "10000000000001",
    "00000000000000",
    "01010101010101"
  ], "impl test 16 (9x14)");

  CheckImpl(9, 20, [
    "01010101010101010101",
    "00000000000000000000",
    "10000000000000000001",
    "00000000000000000000",
    "10000000000000000001",
    "00000000000000000000",
    "10000000000000000001",
    "00000000000000000000",
    "01010101010101010101"
  ], "impl test 17 (9x20)");

  CheckImpl(10, 5, [
    "10101",
    "00000",
    "00001",
    "10000",
    "00001",
    "10000",
    "00001",
    "10000",
    "00001",
    "10100"
  ], "impl test 18 (10x5)");

  CheckImpl(10, 10, [
    "0101010101",
    "0000000000",
    "0000000001",
    "1000000000",
    "0000000001",
    "1000000000",
    "0000000001",
    "1000000000",
    "0000000001",
    "0101010100"
  ], "impl test 19 (10x10)");

  CheckImpl(10, 17, [
    "10101010101010101",
    "00000000000000000",
    "00000000000000001",
    "10000000000000000",
    "00000000000000001",
    "10000000000000000",
    "00000000000000001",
    "10000000000000000",
    "00000000000000001",
    "10101010101010100"
  ], "impl test 20 (10x17)");

  CheckImpl(11, 4, [
    "0101",
    "0000",
    "1001",
    "0000",
    "1001",
    "0000",
    "1001",
    "0000",
    "1001",
    "0000",
    "0101"
  ], "impl test 21 (11x4)");

  CheckImpl(11, 8, [
    "01010101",
    "00000000",
    "10000001",
    "00000000",
    "10000001",
    "00000000",
    "10000001",
    "00000000",
    "10000001",
    "00000000",
    "01010101"
  ], "impl test 22 (11x8)");

  CheckImpl(11, 16, [
    "0101010101010101",
    "0000000000000000",
    "1000000000000001",
    "0000000000000000",
    "1000000000000001",
    "0000000000000000",
    "1000000000000001",
    "0000000000000000",
    "1000000000000001",
    "0000000000000000",
    "0101010101010101"
  ], "impl test 23 (11x16)");

  CheckImpl(12, 4, [
    "0101",
    "0000",
    "0001",
    "1000",
    "0001",
    "1000",
    "0001",
    "1000",
    "0001",
    "1000",
    "0001",
    "0100"
  ], "impl test 24 (12x4)");

  CheckImpl(12, 11, [
    "10101010101",
    "00000000000",
    "00000000001",
    "10000000000",
    "00000000001",
    "10000000000",
    "00000000001",
    "10000000000",
    "00000000001",
    "10000000000",
    "00000000001",
    "10101010100"
  ], "impl test 25 (12x11)");

  CheckImpl(13, 5, [
    "10101",
    "00000",
    "10001",
    "00000",
    "10001",
    "00000",
    "10001",
    "00000",
    "10001",
    "00000",
    "10001",
    "00000",
    "10101"
  ], "impl test 26 (13x5)");

  CheckImpl(13, 11, [
    "10101010101",
    "00000000000",
    "10000000001",
    "00000000000",
    "10000000001",
    "00000000000",
    "10000000001",
    "00000000000",
    "10000000001",
    "00000000000",
    "10000000001",
    "00000000000",
    "10101010101"
  ], "impl test 27 (13x11)");

  CheckImpl(13, 20, [
    "01010101010101010101",
    "00000000000000000000",
    "10000000000000000001",
    "00000000000000000000",
    "10000000000000000001",
    "00000000000000000000",
    "10000000000000000001",
    "00000000000000000000",
    "10000000000000000001",
    "00000000000000000000",
    "10000000000000000001",
    "00000000000000000000",
    "01010101010101010101"
  ], "impl test 28 (13x20)");

  CheckImpl(14, 9, [
    "101010101",
    "000000000",
    "000000001",
    "100000000",
    "000000001",
    "100000000",
    "000000001",
    "100000000",
    "000000001",
    "100000000",
    "000000001",
    "100000000",
    "000000001",
    "101010100"
  ], "impl test 29 (14x9)");

  CheckImpl(14, 10, [
    "0101010101",
    "0000000000",
    "0000000001",
    "1000000000",
    "0000000001",
    "1000000000",
    "0000000001",
    "1000000000",
    "0000000001",
    "1000000000",
    "0000000001",
    "1000000000",
    "0000000001",
    "0101010100"
  ], "impl test 30 (14x10)");

  CheckImpl(14, 17, [
    "10101010101010101",
    "00000000000000000",
    "00000000000000001",
    "10000000000000000",
    "00000000000000001",
    "10000000000000000",
    "00000000000000001",
    "10000000000000000",
    "00000000000000001",
    "10000000000000000",
    "00000000000000001",
    "10000000000000000",
    "00000000000000001",
    "10101010101010100"
  ], "impl test 31 (14x17)");

  CheckImpl(15, 6, [
    "010101",
    "000000",
    "100001",
    "000000",
    "100001",
    "000000",
    "100001",
    "000000",
    "100001",
    "000000",
    "100001",
    "000000",
    "100001",
    "000000",
    "010101"
  ], "impl test 32 (15x6)");

  CheckImpl(15, 9, [
    "101010101",
    "000000000",
    "100000001",
    "000000000",
    "100000001",
    "000000000",
    "100000001",
    "000000000",
    "100000001",
    "000000000",
    "100000001",
    "000000000",
    "100000001",
    "000000000",
    "101010101"
  ], "impl test 33 (15x9)");

  CheckImpl(16, 11, [
    "10101010101",
    "00000000000",
    "00000000001",
    "10000000000",
    "00000000001",
    "10000000000",
    "00000000001",
    "10000000000",
    "00000000001",
    "10000000000",
    "00000000001",
    "10000000000",
    "00000000001",
    "10000000000",
    "00000000001",
    "10101010100"
  ], "impl test 34 (16x11)");

  CheckImpl(18, 17, [
    "10101010101010101",
    "00000000000000000",
    "00000000000000001",
    "10000000000000000",
    "00000000000000001",
    "10000000000000000",
    "00000000000000001",
    "10000000000000000",
    "00000000000000001",
    "10000000000000000",
    "00000000000000001",
    "10000000000000000",
    "00000000000000001",
    "10000000000000000",
    "00000000000000001",
    "10000000000000000",
    "00000000000000001",
    "10101010101010100"
  ], "impl test 35 (18x17)");

  CheckImpl(19, 18, [
    "010101010101010101",
    "000000000000000000",
    "100000000000000001",
    "000000000000000000",
    "100000000000000001",
    "000000000000000000",
    "100000000000000001",
    "000000000000000000",
    "100000000000000001",
    "000000000000000000",
    "100000000000000001",
    "000000000000000000",
    "100000000000000001",
    "000000000000000000",
    "100000000000000001",
    "000000000000000000",
    "100000000000000001",
    "000000000000000000",
    "010101010101010101"
  ], "impl test 36 (19x18)");

  CheckImpl(20, 3, [
    "101",
    "000",
    "001",
    "100",
    "001",
    "100",
    "001",
    "100",
    "001",
    "100",
    "001",
    "100",
    "001",
    "100",
    "001",
    "100",
    "001",
    "100",
    "001",
    "100"
  ], "impl test 37 (20x3)");

  CheckImpl(20, 14, [
    "01010101010101",
    "00000000000000",
    "00000000000001",
    "10000000000000",
    "00000000000001",
    "10000000000000",
    "00000000000001",
    "10000000000000",
    "00000000000001",
    "10000000000000",
    "00000000000001",
    "10000000000000",
    "00000000000001",
    "10000000000000",
    "00000000000001",
    "10000000000000",
    "00000000000001",
    "10000000000000",
    "00000000000001",
    "01010101010100"
  ], "impl test 38 (20x14)");

  CheckImpl(20, 20, [
    "01010101010101010101",
    "00000000000000000000",
    "00000000000000000001",
    "10000000000000000000",
    "00000000000000000001",
    "10000000000000000000",
    "00000000000000000001",
    "10000000000000000000",
    "00000000000000000001",
    "10000000000000000000",
    "00000000000000000001",
    "10000000000000000000",
    "00000000000000000001",
    "10000000000000000000",
    "00000000000000000001",
    "10000000000000000000",
    "00000000000000000001",
    "10000000000000000000",
    "00000000000000000001",
    "01010101010101010100"
  ], "impl test 39 (20x20)");

  print "All tests passed\n";
}