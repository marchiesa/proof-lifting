// ── Problem-modeling predicates ──

predicate IsGrid(grid: seq<seq<char>>, n: int, m: int)
{
  n >= 0 && m >= 0 && |grid| == n &&
  forall i | 0 <= i < n :: |grid[i]| == m
}

predicate ValidInput(grid: seq<seq<char>>, n: int, m: int)
{
  IsGrid(grid, n, m) &&
  forall i, j | 0 <= i < n && 0 <= j < m ::
    grid[i][j] == 'R' || grid[i][j] == 'W' || grid[i][j] == '.'
}

predicate FullyColored(grid: seq<seq<char>>, n: int, m: int)
{
  IsGrid(grid, n, m) &&
  forall i, j | 0 <= i < n && 0 <= j < m ::
    grid[i][j] == 'R' || grid[i][j] == 'W'
}

predicate NeighborsAlternate(grid: seq<seq<char>>, n: int, m: int)
{
  IsGrid(grid, n, m) &&
  (forall i, j | 0 <= i < n && 0 <= j < m - 1 :: grid[i][j] != grid[i][j + 1]) &&
  (forall i, j | 0 <= i < n - 1 && 0 <= j < m :: grid[i][j] != grid[i + 1][j])
}

predicate ExtendsInput(coloring: seq<seq<char>>, input: seq<seq<char>>, n: int, m: int)
{
  IsGrid(coloring, n, m) && IsGrid(input, n, m) &&
  forall i, j | 0 <= i < n && 0 <= j < m ::
    input[i][j] != '.' ==> coloring[i][j] == input[i][j]
}

predicate IsSolution(coloring: seq<seq<char>>, input: seq<seq<char>>, n: int, m: int)
{
  FullyColored(coloring, n, m) &&
  NeighborsAlternate(coloring, n, m) &&
  ExtendsInput(coloring, input, n, m)
}

// ── Candidate enumeration ──

function CellColor(i: int, j: int, w: int): char
  requires w == 0 || w == 1
{
  if (i + j) % 2 == w then 'R' else 'W'
}

function BuildRow(row: int, len: int, w: int): seq<char>
  requires len >= 0
  requires w == 0 || w == 1
  decreases len
{
  if len == 0 then []
  else BuildRow(row, len - 1, w) + [CellColor(row, len - 1, w)]
}

function BuildGrid(n: int, m: int, w: int): seq<seq<char>>
  requires n >= 0 && m >= 0
  requires w == 0 || w == 1
  decreases n
{
  if n == 0 then []
  else BuildGrid(n - 1, m, w) + [BuildRow(n - 1, m, w)]
}

method ColourTheFlag(grid: seq<seq<char>>, n: int, m: int) returns (possible: bool, result: seq<seq<char>>)
  requires ValidInput(grid, n, m)
  ensures possible ==> IsSolution(result, grid, n, m)
  ensures !possible ==> result == []
  ensures possible == (exists w | 0 <= w <= 1 :: IsSolution(BuildGrid(n, m, w), grid, n, m))
{
  var w := 0;
  var i := 0;
  while i < n {
    var j := 0;
    while j < m {
      if grid[i][j] == 'R' {
        w := (i + j) % 2;
      } else if grid[i][j] == 'W' {
        w := 1 - (i + j) % 2;
      }
      j := j + 1;
    }
    i := i + 1;
  }

  var bad := false;
  result := [];
  i := 0;
  while i < n {
    var row: seq<char> := [];
    var j := 0;
    while j < m {
      var c: char;
      if (i + j) % 2 == w {
        c := 'R';
      } else {
        c := 'W';
      }
      if grid[i][j] != '.' && c != grid[i][j] {
        bad := true;
      }
      row := row + [c];
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }

  if bad {
    possible := false;
    result := [];
  } else {
    possible := true;
  }
}

method Main()
{
  // =========================================
  // SPEC POSITIVE TESTS
  // =========================================
  // IsSolution(correct_result, input, n, m) should hold

  // Test 3: 1x1 blank → R
  expect IsSolution(["R"], ["."], 1, 1), "spec positive 1 (Test 3)";

  // Test 5: 1x1 R → R
  expect IsSolution(["R"], ["R"], 1, 1), "spec positive 2 (Test 5)";

  // Test 6: 1x1 W → W
  expect IsSolution(["W"], ["W"], 1, 1), "spec positive 3 (Test 6)";

  // Test 7: 2x2 blank → RW/WR
  expect IsSolution(["RW", "WR"], ["..", ".."], 2, 2), "spec positive 4 (Test 7)";

  // Test 2: 3x1 .R. → WRW
  expect IsSolution(["W", "R", "W"], [".", "R", "."], 3, 1), "spec positive 5 (Test 2)";

  // Test 10: 3x3 R.R/.../R.R → RWR/WRW/RWR
  expect IsSolution(["RWR", "WRW", "RWR"], ["R.R", "...", "R.R"], 3, 3), "spec positive 6 (Test 10)";

  // Test 13.1: 2x2 already valid RW/WR
  expect IsSolution(["RW", "WR"], ["RW", "WR"], 2, 2), "spec positive 7 (Test 13.1)";

  // Test 13.2: 1x3 blank → RWR
  expect IsSolution(["RWR"], ["..."], 1, 3), "spec positive 8 (Test 13.2)";

  // Test 13.3: 3x1 blank → R/W/R
  expect IsSolution(["R", "W", "R"], [".", ".", "."], 3, 1), "spec positive 9 (Test 13.3)";

  // Test 12.2: 3x2 blank → RW/WR/RW
  expect IsSolution(["RW", "WR", "RW"], ["..", "..", ".."], 3, 2), "spec positive 10 (Test 12.2)";

  // Test 8: 3x3 conflicting → NO: both checkerboard candidates fail
  expect !IsSolution(BuildGrid(3, 3, 0), ["R.W", "...", "W.R"], 3, 3), "spec positive 11a (Test 8, w=0)";
  expect !IsSolution(BuildGrid(3, 3, 1), ["R.W", "...", "W.R"], 3, 3), "spec positive 11b (Test 8, w=1)";

  // =========================================
  // SPEC NEGATIVE TESTS
  // =========================================
  // IsSolution with wrong outputs should be false

  // Neg 3: 1x1 "." → wrong result "R WRONG" (row length 7 != m=1, IsGrid fails)
  expect !IsSolution(["R WRONG"], ["."], 1, 1), "spec negative 1 (Neg 3)";

  // Neg 5: 1x1 "R" → wrong result "R WRONG"
  expect !IsSolution(["R WRONG"], ["R"], 1, 1), "spec negative 2 (Neg 5)";

  // Neg 6: 1x1 "W" → wrong result "W WRONG"
  expect !IsSolution(["W WRONG"], ["W"], 1, 1), "spec negative 3 (Neg 6)";

  // Neg 7: 2x2 blank → wrong last row "WR WRONG"
  expect !IsSolution(["RW", "WR WRONG"], ["..", ".."], 2, 2), "spec negative 4 (Neg 7)";

  // Neg 2: 3x1 .R. → wrong last row "W WRONG"
  expect !IsSolution(["W", "R", "W WRONG"], [".", "R", "."], 3, 1), "spec negative 5 (Neg 2)";

  // Neg 8: 3x3 R.W/.../W.R → wrong claims possible=true, but no coloring works
  expect !IsSolution(["RWR", "WRW", "RWR"], ["R.W", "...", "W.R"], 3, 3), "spec negative 6a (Neg 8)";
  expect !IsSolution(["WRW", "RWR", "WRW"], ["R.W", "...", "W.R"], 3, 3), "spec negative 6b (Neg 8)";

  // Neg 10: 3x3 → wrong last row "RWR WRONG"
  expect !IsSolution(["RWR", "WRW", "RWR WRONG"], ["R.R", "...", "R.R"], 3, 3), "spec negative 7 (Neg 10)";

  // Neg 9 scaled to 1x3: "R.W" has same conflict pattern as 1x5 "R.W.R"
  expect !IsSolution(BuildGrid(1, 3, 0), ["R.W"], 1, 3), "spec negative 8a (Neg 9 scaled, w=0)";
  expect !IsSolution(BuildGrid(1, 3, 1), ["R.W"], 1, 3), "spec negative 8b (Neg 9 scaled, w=1)";

  // =========================================
  // IMPLEMENTATION TESTS
  // =========================================

  // Test 1.1: 4x6 grid with R and W hints
  var p1, r1 := ColourTheFlag([".R....", "......", "......", ".W...."], 4, 6);
  expect p1 == true, "impl test 1.1: expected YES";
  expect r1 == ["WRWRWR", "RWRWRW", "WRWRWR", "RWRWRW"], "impl test 1.1: wrong result";

  // Test 1.2: 4x4 conflicting
  var p2, r2 := ColourTheFlag([".R.W", "....", "....", "...."], 4, 4);
  expect p2 == false, "impl test 1.2: expected NO";
  expect r2 == [], "impl test 1.2: result should be empty";

  // Test 1.3: 5x1 already filled
  var p3, r3 := ColourTheFlag(["R", "W", "R", "W", "R"], 5, 1);
  expect p3 == true, "impl test 1.3: expected YES";
  expect r3 == ["R", "W", "R", "W", "R"], "impl test 1.3: wrong result";

  // Test 2: 3x1 with R in middle
  var p4, r4 := ColourTheFlag([".", "R", "."], 3, 1);
  expect p4 == true, "impl test 2: expected YES";
  expect r4 == ["W", "R", "W"], "impl test 2: wrong result";

  // Test 3: 1x1 blank
  var p5, r5 := ColourTheFlag(["."], 1, 1);
  expect p5 == true, "impl test 3: expected YES";
  expect r5 == ["R"], "impl test 3: wrong result";

  // Test 4: 5x5 with W in corner
  var p6, r6 := ColourTheFlag([".....", ".....", ".....", ".....", "....W"], 5, 5);
  expect p6 == true, "impl test 4: expected YES";
  expect r6 == ["WRWRW", "RWRWR", "WRWRW", "RWRWR", "WRWRW"], "impl test 4: wrong result";

  // Test 5: 1x1 R
  var p7, r7 := ColourTheFlag(["R"], 1, 1);
  expect p7 == true, "impl test 5: expected YES";
  expect r7 == ["R"], "impl test 5: wrong result";

  // Test 6: 1x1 W
  var p8, r8 := ColourTheFlag(["W"], 1, 1);
  expect p8 == true, "impl test 6: expected YES";
  expect r8 == ["W"], "impl test 6: wrong result";

  // Test 7: 2x2 all blank
  var p9, r9 := ColourTheFlag(["..", ".."], 2, 2);
  expect p9 == true, "impl test 7: expected YES";
  expect r9 == ["RW", "WR"], "impl test 7: wrong result";

  // Test 8: 3x3 conflicting corners
  var p10, r10 := ColourTheFlag(["R.W", "...", "W.R"], 3, 3);
  expect p10 == false, "impl test 8: expected NO";
  expect r10 == [], "impl test 8: result should be empty";

  // Test 9: 1x5 conflicting row
  var p11, r11 := ColourTheFlag(["R.W.R"], 1, 5);
  expect p11 == false, "impl test 9: expected NO";
  expect r11 == [], "impl test 9: result should be empty";

  // Test 10: 3x3 R in corners
  var p12, r12 := ColourTheFlag(["R.R", "...", "R.R"], 3, 3);
  expect p12 == true, "impl test 10: expected YES";
  expect r12 == ["RWR", "WRW", "RWR"], "impl test 10: wrong result";

  // Test 11: 4x3 with R and W in center
  var p13, r13 := ColourTheFlag(["...", ".R.", ".W.", "..."], 4, 3);
  expect p13 == true, "impl test 11: expected YES";
  expect r13 == ["RWR", "WRW", "RWR", "WRW"], "impl test 11: wrong result";

  // Test 12.1: 2x3 conflicting
  var p14, r14 := ColourTheFlag(["R.W", "W.R"], 2, 3);
  expect p14 == false, "impl test 12.1: expected NO";
  expect r14 == [], "impl test 12.1: result should be empty";

  // Test 12.2: 3x2 all blank
  var p15, r15 := ColourTheFlag(["..", "..", ".."], 3, 2);
  expect p15 == true, "impl test 12.2: expected YES";
  expect r15 == ["RW", "WR", "RW"], "impl test 12.2: wrong result";

  // Test 13.1: 2x2 already valid
  var p16, r16 := ColourTheFlag(["RW", "WR"], 2, 2);
  expect p16 == true, "impl test 13.1: expected YES";
  expect r16 == ["RW", "WR"], "impl test 13.1: wrong result";

  // Test 13.2: 1x3 all blank
  var p17, r17 := ColourTheFlag(["..."], 1, 3);
  expect p17 == true, "impl test 13.2: expected YES";
  expect r17 == ["RWR"], "impl test 13.2: wrong result";

  // Test 13.3: 3x1 all blank
  var p18, r18 := ColourTheFlag([".", ".", "."], 3, 1);
  expect p18 == true, "impl test 13.3: expected YES";
  expect r18 == ["R", "W", "R"], "impl test 13.3: wrong result";

  print "All tests passed\n";
}