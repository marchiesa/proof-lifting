predicate ValidGrid(grid: seq<seq<char>>)
{
  |grid| == 3 && forall i | 0 <= i < 3 :: |grid[i]| == 3
}

predicate SymmetricAboutCenter(grid: seq<seq<char>>)
  requires ValidGrid(grid)
{
  forall i, j | 0 <= i < 3 && 0 <= j < 3 ::
    grid[i][j] == 'X' ==> grid[2 - i][2 - j] == 'X'
}

method {:verify false} SuperAgent(grid: seq<seq<char>>) returns (symmetric: bool)
  requires ValidGrid(grid)
  ensures symmetric == SymmetricAboutCenter(grid)
{
  var bad := false;
  var i := 0;
  while i < 3 {
    var j := 0;
    while j < 3 {
      if grid[i][j] == 'X' && grid[2 - i][2 - j] != 'X' {
        bad := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  symmetric := !bad;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Verify SymmetricAboutCenter(grid) == correct_output for each positive pair

  expect SymmetricAboutCenter([['X','X','.'], ['.','.','.'], ['.','X','X']]) == true,  "spec positive 1";
  expect SymmetricAboutCenter([['X','.','X'], ['X','.','.'], ['.','.','.']]) == false, "spec positive 2";
  expect SymmetricAboutCenter([['.','.','.'], ['.','.','.'], ['.','.','.']]) == true,  "spec positive 3";
  expect SymmetricAboutCenter([['.','X','.'], ['.','X','.'], ['.','X','.']]) == true,  "spec positive 4";
  expect SymmetricAboutCenter([['X','X','X'], ['X','X','X'], ['X','X','X']]) == true,  "spec positive 5";
  expect SymmetricAboutCenter([['X','X','X'], ['X','.','X'], ['X','X','X']]) == true,  "spec positive 6";
  expect SymmetricAboutCenter([['X','.','.'], ['.','X','.'], ['.','.','X']]) == true,  "spec positive 7";
  expect SymmetricAboutCenter([['.','.','.'], ['X','.','X'], ['X','.','.']]) == false, "spec positive 8";
  expect SymmetricAboutCenter([['.','X','.'], ['X','.','X'], ['.','X','.']]) == true,  "spec positive 9";
  expect SymmetricAboutCenter([['X','.','X'], ['.','X','.'], ['X','.','X']]) == true,  "spec positive 10";

  // ===== SPEC NEGATIVE TESTS =====
  // Verify SymmetricAboutCenter(grid) != wrong_output for each negative pair

  expect !(SymmetricAboutCenter([['X','X','.'], ['.','.','.'], ['.','X','X']]) == false), "spec negative 1";
  expect !(SymmetricAboutCenter([['X','.','X'], ['X','.','.'], ['.','.','.']]) == true),  "spec negative 2";
  expect !(SymmetricAboutCenter([['.','.','.'], ['.','.','.'], ['.','.','.']]) == false), "spec negative 3";
  expect !(SymmetricAboutCenter([['.','X','.'], ['.','X','.'], ['.','X','.']]) == false), "spec negative 4";
  expect !(SymmetricAboutCenter([['X','X','X'], ['X','X','X'], ['X','X','X']]) == false), "spec negative 5";
  expect !(SymmetricAboutCenter([['X','X','X'], ['X','.','X'], ['X','X','X']]) == false), "spec negative 6";
  expect !(SymmetricAboutCenter([['X','.','.'], ['.','X','.'], ['.','.','X']]) == false), "spec negative 7";
  expect !(SymmetricAboutCenter([['.','.','.'], ['X','.','X'], ['X','.','.']]) == true),  "spec negative 8";
  expect !(SymmetricAboutCenter([['.','X','.'], ['X','.','X'], ['.','X','.']]) == false), "spec negative 9";
  expect !(SymmetricAboutCenter([['X','.','X'], ['.','X','.'], ['X','.','X']]) == false), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  // Call SuperAgent and verify returned value matches expected output

  var r1 := SuperAgent([['X','X','.'], ['.','.','.'], ['.','X','X']]);
  expect r1 == true,  "impl test 1 failed";

  var r2 := SuperAgent([['X','.','X'], ['X','.','.'], ['.','.','.']]);
  expect r2 == false, "impl test 2 failed";

  var r3 := SuperAgent([['.','.','.'], ['.','.','.'], ['.','.','.']]);
  expect r3 == true,  "impl test 3 failed";

  var r4 := SuperAgent([['.','X','.'], ['.','X','.'], ['.','X','.']]);
  expect r4 == true,  "impl test 4 failed";

  var r5 := SuperAgent([['X','X','X'], ['X','X','X'], ['X','X','X']]);
  expect r5 == true,  "impl test 5 failed";

  var r6 := SuperAgent([['X','X','X'], ['X','.','X'], ['X','X','X']]);
  expect r6 == true,  "impl test 6 failed";

  var r7 := SuperAgent([['X','.','.'], ['.','X','.'], ['.','.','X']]);
  expect r7 == true,  "impl test 7 failed";

  var r8 := SuperAgent([['.','.','.'], ['X','.','X'], ['X','.','.']]);
  expect r8 == false, "impl test 8 failed";

  var r9 := SuperAgent([['.','X','.'], ['X','.','X'], ['.','X','.']]);
  expect r9 == true,  "impl test 9 failed";

  var r10 := SuperAgent([['X','.','X'], ['.','X','.'], ['X','.','X']]);
  expect r10 == true, "impl test 10 failed";

  var r11 := SuperAgent([['.','.','.'], ['.','.','.'], ['.','.','X']]);
  expect r11 == false, "impl test 11 failed";

  var r12 := SuperAgent([['.','.','.'], ['.','X','.'], ['.','.','.']]);
  expect r12 == true,  "impl test 12 failed";

  var r13 := SuperAgent([['X','X','X'], ['.','.','.'], ['X','X','X']]);
  expect r13 == true,  "impl test 13 failed";

  var r14 := SuperAgent([['.','.','.'], ['X','X','X'], ['.','.','.']]);
  expect r14 == true,  "impl test 14 failed";

  var r15 := SuperAgent([['.','.','X'], ['X','.','.'], ['.','.','X']]);
  expect r15 == false, "impl test 15 failed";

  var r16 := SuperAgent([['.','X','.'], ['.','.','.'], ['X','.','X']]);
  expect r16 == false, "impl test 16 failed";

  var r17 := SuperAgent([['X','.','X'], ['X','.','X'], ['X','.','X']]);
  expect r17 == true,  "impl test 17 failed";

  var r18 := SuperAgent([['.','X','.'], ['X','.','X'], ['X','X','.']]);
  expect r18 == false, "impl test 18 failed";

  var r19 := SuperAgent([['.','.','.'], ['X','X','X'], ['X','X','X']]);
  expect r19 == false, "impl test 19 failed";

  var r20 := SuperAgent([['.','.','.'], ['X','.','X'], ['.','.','.']]);
  expect r20 == true,  "impl test 20 failed";

  print "All tests passed\n";
}