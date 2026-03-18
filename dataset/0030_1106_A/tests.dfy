predicate ValidMatrix(M: seq<seq<char>>, n: int)
{
  n >= 0 &&
  |M| == n &&
  (forall i | 0 <= i < n :: |M[i]| == n)
}

predicate IsCrossAt(M: seq<seq<char>>, n: int, a: int, b: int)
  requires ValidMatrix(M, n)
  requires 0 <= a < n && 0 <= b < n
{
  1 <= a <= n - 2 &&
  1 <= b <= n - 2 &&
  M[a][b] == 'X' &&
  M[a-1][b-1] == 'X' &&
  M[a-1][b+1] == 'X' &&
  M[a+1][b-1] == 'X' &&
  M[a+1][b+1] == 'X'
}

function CrossCount(M: seq<seq<char>>, n: int): int
  requires ValidMatrix(M, n)
{
  |set a, b | 0 <= a < n && 0 <= b < n && IsCrossAt(M, n, a, b) :: (a, b)|
}

method CountCrosses(n: int, M: seq<seq<char>>) returns (count: int)
  requires ValidMatrix(M, n)
  ensures count == CrossCount(M, n)
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
  // ===== SPEC POSITIVE TESTS (small inputs, testing CrossCount) =====

  // From Test 4: n=1, ["X"] -> 0
  var sp1: seq<seq<char>> := ["X"];
  expect CrossCount(sp1, 1) == 0, "spec positive 1";

  // From Test 5: n=1, ["."] -> 0
  var sp2: seq<seq<char>> := ["."];
  expect CrossCount(sp2, 1) == 0, "spec positive 2";

  // From Test 2: n=2, ["XX","XX"] -> 0
  var sp3: seq<seq<char>> := ["XX", "XX"];
  expect CrossCount(sp3, 2) == 0, "spec positive 3";

  // From Test 6: n=2, [".X","X."] -> 0
  var sp4: seq<seq<char>> := [".X", "X."];
  expect CrossCount(sp4, 2) == 0, "spec positive 4";

  // From Test 7: n=2, ["..",".."] -> 0
  var sp5: seq<seq<char>> := ["..", ".."];
  expect CrossCount(sp5, 2) == 0, "spec positive 5";

  // From Test 8: n=3, ["...",".X.","..."] -> 0
  var sp6: seq<seq<char>> := ["...", ".X.", "..."];
  expect CrossCount(sp6, 3) == 0, "spec positive 6";

  // Extra: n=3 cross pattern ["X.X",".X.","X.X"] -> 1
  var sp7: seq<seq<char>> := ["X.X", ".X.", "X.X"];
  expect CrossCount(sp7, 3) == 1, "spec positive 7";

  // ===== SPEC NEGATIVE TESTS (small inputs, testing CrossCount != wrong) =====

  // From Negative 4: n=1, ["X"], wrong=1
  var sn1: seq<seq<char>> := ["X"];
  expect CrossCount(sn1, 1) != 1, "spec negative 1";

  // From Negative 5: n=1, ["."], wrong=1
  var sn2: seq<seq<char>> := ["."];
  expect CrossCount(sn2, 1) != 1, "spec negative 2";

  // From Negative 2: n=2, ["XX","XX"], wrong=1
  var sn3: seq<seq<char>> := ["XX", "XX"];
  expect CrossCount(sn3, 2) != 1, "spec negative 3";

  // From Negative 6: n=2, [".X","X."], wrong=1
  var sn4: seq<seq<char>> := [".X", "X."];
  expect CrossCount(sn4, 2) != 1, "spec negative 4";

  // From Negative 7: n=2, ["..",".."], wrong=1
  var sn5: seq<seq<char>> := ["..", ".."];
  expect CrossCount(sn5, 2) != 1, "spec negative 5";

  // From Negative 8: n=3, ["...",".X.","..."], wrong=1
  var sn6: seq<seq<char>> := ["...", ".X.", "..."];
  expect CrossCount(sn6, 3) != 1, "spec negative 6";

  // Extra: n=3 cross ["X.X",".X.","X.X"], wrong=0 (correct is 1)
  var sn7: seq<seq<char>> := ["X.X", ".X.", "X.X"];
  expect CrossCount(sn7, 3) != 0, "spec negative 7";

  // ===== IMPLEMENTATION TESTS (full-size inputs) =====

  // Test 1: n=5
  var m1: seq<seq<char>> := [".....", ".XXX.", ".XXX.", ".XXX.", "....."];
  var r1 := CountCrosses(5, m1);
  expect r1 == 1, "impl test 1 failed";

  // Test 2: n=2
  var m2: seq<seq<char>> := ["XX", "XX"];
  var r2 := CountCrosses(2, m2);
  expect r2 == 0, "impl test 2 failed";

  // Test 3: n=6
  var m3: seq<seq<char>> := ["......", "X.X.X.", ".X.X.X", "X.X.X.", ".X.X.X", "......"];
  var r3 := CountCrosses(6, m3);
  expect r3 == 4, "impl test 3 failed";

  // Test 4: n=1
  var m4: seq<seq<char>> := ["X"];
  var r4 := CountCrosses(1, m4);
  expect r4 == 0, "impl test 4 failed";

  // Test 5: n=1
  var m5: seq<seq<char>> := ["."];
  var r5 := CountCrosses(1, m5);
  expect r5 == 0, "impl test 5 failed";

  // Test 6: n=2
  var m6: seq<seq<char>> := [".X", "X."];
  var r6 := CountCrosses(2, m6);
  expect r6 == 0, "impl test 6 failed";

  // Test 7: n=2
  var m7: seq<seq<char>> := ["..", ".."];
  var r7 := CountCrosses(2, m7);
  expect r7 == 0, "impl test 7 failed";

  // Test 8: n=3
  var m8: seq<seq<char>> := ["...", ".X.", "..."];
  var r8 := CountCrosses(3, m8);
  expect r8 == 0, "impl test 8 failed";

  // Test 9: n=14
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
  expect r9 == 2, "impl test 9 failed";

  print "All tests passed\n";
}