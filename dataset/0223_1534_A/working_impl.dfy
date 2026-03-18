method ColourTheFlag(grid: seq<seq<char>>, n: int, m: int) returns (possible: bool, result: seq<seq<char>>)
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
  // Test 1, sub-case 1: 4x6 grid with R and W hints
  var p1, r1 := ColourTheFlag([".R....", "......", "......", ".W...."], 4, 6);
  expect p1 == true, "Test 1.1: expected YES";
  expect r1 == ["WRWRWR", "RWRWRW", "WRWRWR", "RWRWRW"], "Test 1.1: wrong result";

  // Test 1, sub-case 2: 4x4 grid with conflicting R and W
  var p2, r2 := ColourTheFlag([".R.W", "....", "....", "...."], 4, 4);
  expect p2 == false, "Test 1.2: expected NO";

  // Test 1, sub-case 3: 5x1 column already filled
  var p3, r3 := ColourTheFlag(["R", "W", "R", "W", "R"], 5, 1);
  expect p3 == true, "Test 1.3: expected YES";
  expect r3 == ["R", "W", "R", "W", "R"], "Test 1.3: wrong result";

  // Test 2: 3x1 column with R in middle
  var p4, r4 := ColourTheFlag([".", "R", "."], 3, 1);
  expect p4 == true, "Test 2: expected YES";
  expect r4 == ["W", "R", "W"], "Test 2: wrong result";

  // Test 3: 1x1 blank
  var p5, r5 := ColourTheFlag(["."], 1, 1);
  expect p5 == true, "Test 3: expected YES";
  expect r5 == ["R"], "Test 3: wrong result";

  // Test 4: 5x5 with W in corner
  var p6, r6 := ColourTheFlag([".....", ".....", ".....", ".....", "....W"], 5, 5);
  expect p6 == true, "Test 4: expected YES";
  expect r6 == ["WRWRW", "RWRWR", "WRWRW", "RWRWR", "WRWRW"], "Test 4: wrong result";

  // Test 5: 1x1 R
  var p7, r7 := ColourTheFlag(["R"], 1, 1);
  expect p7 == true, "Test 5: expected YES";
  expect r7 == ["R"], "Test 5: wrong result";

  // Test 6: 1x1 W
  var p8, r8 := ColourTheFlag(["W"], 1, 1);
  expect p8 == true, "Test 6: expected YES";
  expect r8 == ["W"], "Test 6: wrong result";

  // Test 7: 2x2 all blank
  var p9, r9 := ColourTheFlag(["..", ".."], 2, 2);
  expect p9 == true, "Test 7: expected YES";
  expect r9 == ["RW", "WR"], "Test 7: wrong result";

  // Test 8: 3x3 conflicting corners
  var p10, r10 := ColourTheFlag(["R.W", "...", "W.R"], 3, 3);
  expect p10 == false, "Test 8: expected NO";

  // Test 9: 1x5 conflicting row
  var p11, r11 := ColourTheFlag(["R.W.R"], 1, 5);
  expect p11 == false, "Test 9: expected NO";

  // Test 10: 3x3 R in corners
  var p12, r12 := ColourTheFlag(["R.R", "...", "R.R"], 3, 3);
  expect p12 == true, "Test 10: expected YES";
  expect r12 == ["RWR", "WRW", "RWR"], "Test 10: wrong result";

  // Test 11: 4x3 with R and W in center
  var p13, r13 := ColourTheFlag(["...", ".R.", ".W.", "..."], 4, 3);
  expect p13 == true, "Test 11: expected YES";
  expect r13 == ["RWR", "WRW", "RWR", "WRW"], "Test 11: wrong result";

  // Test 12, sub-case 1: 2x3 conflicting
  var p14, r14 := ColourTheFlag(["R.W", "W.R"], 2, 3);
  expect p14 == false, "Test 12.1: expected NO";

  // Test 12, sub-case 2: 3x2 all blank
  var p15, r15 := ColourTheFlag(["..", "..", ".."], 3, 2);
  expect p15 == true, "Test 12.2: expected YES";
  expect r15 == ["RW", "WR", "RW"], "Test 12.2: wrong result";

  // Test 13, sub-case 1: 2x2 already valid
  var p16, r16 := ColourTheFlag(["RW", "WR"], 2, 2);
  expect p16 == true, "Test 13.1: expected YES";
  expect r16 == ["RW", "WR"], "Test 13.1: wrong result";

  // Test 13, sub-case 2: 1x3 all blank
  var p17, r17 := ColourTheFlag(["..."], 1, 3);
  expect p17 == true, "Test 13.2: expected YES";
  expect r17 == ["RWR"], "Test 13.2: wrong result";

  // Test 13, sub-case 3: 3x1 all blank
  var p18, r18 := ColourTheFlag([".", ".", "."], 3, 1);
  expect p18 == true, "Test 13.3: expected YES";
  expect r18 == ["R", "W", "R"], "Test 13.3: wrong result";

  print "All tests passed\n";
}