method CountCrosses(n: int, M: seq<seq<char>>) returns (count: int)
{
  count := 0;
  if n < 3 {
    return;
  }
  var a := 1;
  while a < n - 1
  {
    var b := 1;
    while b < n - 1
    {
      if M[a][b] == 'X'
         && M[a-1][b-1] == 'X'
         && M[a-1][b+1] == 'X'
         && M[a+1][b-1] == 'X'
         && M[a+1][b+1] == 'X'
      {
        count := count + 1;
      }
      b := b + 1;
    }
    a := a + 1;
  }
}

method Main()
{
  // Test 1
  var m1: seq<seq<char>> := [".....", ".XXX.", ".XXX.", ".XXX.", "....."];
  var r1 := CountCrosses(5, m1);
  expect r1 == 1, "Test 1 failed";

  // Test 2
  var m2: seq<seq<char>> := ["XX", "XX"];
  var r2 := CountCrosses(2, m2);
  expect r2 == 0, "Test 2 failed";

  // Test 3
  var m3: seq<seq<char>> := ["......", "X.X.X.", ".X.X.X", "X.X.X.", ".X.X.X", "......"];
  var r3 := CountCrosses(6, m3);
  expect r3 == 4, "Test 3 failed";

  // Test 4
  var m4: seq<seq<char>> := ["X"];
  var r4 := CountCrosses(1, m4);
  expect r4 == 0, "Test 4 failed";

  // Test 5
  var m5: seq<seq<char>> := ["."];
  var r5 := CountCrosses(1, m5);
  expect r5 == 0, "Test 5 failed";

  // Test 6
  var m6: seq<seq<char>> := [".X", "X."];
  var r6 := CountCrosses(2, m6);
  expect r6 == 0, "Test 6 failed";

  // Test 7
  var m7: seq<seq<char>> := ["..", ".."];
  var r7 := CountCrosses(2, m7);
  expect r7 == 0, "Test 7 failed";

  // Test 8
  var m8: seq<seq<char>> := ["...", ".X.", "..."];
  var r8 := CountCrosses(3, m8);
  expect r8 == 0, "Test 8 failed";

  // Test 9
  var m9: seq<seq<char>> := [
    "XXX.XXXXX..X.X",
    "X..XX..X...X..",
    ".....X.XX..XXX",
    ".X..X..XXX.XX.",
    "...XXXX.XX..XX",
    ".X..XX...XXX..",
    "XX.XX.XX..XXX.",
    ".X..X.....X.XX",
    "...XXX...XX.XX",
    "XXX.XX.XX.X.XX",
    "X.XXXX..XX.XX.",
    ".X.XX....X....",
    "X..XX..X.XX.X.",
    "..X...XX....XX"
  ];
  var r9 := CountCrosses(14, m9);
  expect r9 == 2, "Test 9 failed";

  print "All tests passed\n";
}