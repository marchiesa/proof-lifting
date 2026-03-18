method SuperAgent(grid: seq<seq<char>>) returns (symmetric: bool)
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
  // Test 1: YES
  var r1 := SuperAgent([['X','X','.'], ['.','.','.'],['.','X','X']]);
  expect r1 == true, "Test 1 failed";

  // Test 2: NO
  var r2 := SuperAgent([['X','.','X'], ['X','.','.'],['.','.','.']] );
  expect r2 == false, "Test 2 failed";

  // Test 3: YES
  var r3 := SuperAgent([['.','.','.'], ['.','.','.'],['.','.','.']]);
  expect r3 == true, "Test 3 failed";

  // Test 4: YES
  var r4 := SuperAgent([['.','X','.'], ['.','X','.'],['.','X','.']]);
  expect r4 == true, "Test 4 failed";

  // Test 5: YES
  var r5 := SuperAgent([['X','X','X'], ['X','X','X'],['X','X','X']]);
  expect r5 == true, "Test 5 failed";

  // Test 6: YES
  var r6 := SuperAgent([['X','X','X'], ['X','.','X'],['X','X','X']]);
  expect r6 == true, "Test 6 failed";

  // Test 7: YES
  var r7 := SuperAgent([['X','.','.'], ['.','X','.'],['.','.','X']]);
  expect r7 == true, "Test 7 failed";

  // Test 8: NO
  var r8 := SuperAgent([['.','.','.'], ['X','.','X'],['X','.','.']]);
  expect r8 == false, "Test 8 failed";

  // Test 9: YES
  var r9 := SuperAgent([['.','X','.'], ['X','.','X'],['.','X','.']]);
  expect r9 == true, "Test 9 failed";

  // Test 10: YES
  var r10 := SuperAgent([['X','.','X'], ['.','X','.'],['X','.','X']]);
  expect r10 == true, "Test 10 failed";

  // Test 11: NO
  var r11 := SuperAgent([['.','.','.'], ['.','.','.'],['.','.','X']]);
  expect r11 == false, "Test 11 failed";

  // Test 12: YES
  var r12 := SuperAgent([['.','.','.'], ['.','X','.'],['.','.','.']]);
  expect r12 == true, "Test 12 failed";

  // Test 13: YES
  var r13 := SuperAgent([['X','X','X'], ['.','.','.'],['X','X','X']]);
  expect r13 == true, "Test 13 failed";

  // Test 14: YES
  var r14 := SuperAgent([['.','.','.'], ['X','X','X'],['.','.','.']]);
  expect r14 == true, "Test 14 failed";

  // Test 15: NO
  var r15 := SuperAgent([['.','.','X'], ['X','.','.'],['.','.','X']]);
  expect r15 == false, "Test 15 failed";

  // Test 16: NO
  var r16 := SuperAgent([['.','X','.'], ['.','.','.'],['X','.','X']]);
  expect r16 == false, "Test 16 failed";

  // Test 17: YES
  var r17 := SuperAgent([['X','.','X'], ['X','.','X'],['X','.','X']]);
  expect r17 == true, "Test 17 failed";

  // Test 18: NO
  var r18 := SuperAgent([['.','X','.'], ['X','.','X'],['X','X','.']]);
  expect r18 == false, "Test 18 failed";

  // Test 19: NO
  var r19 := SuperAgent([['.','.','.'], ['X','X','X'],['X','X','X']]);
  expect r19 == false, "Test 19 failed";

  // Test 20: YES
  var r20 := SuperAgent([['.','.','.'], ['X','.','X'],['.','.','.']]);
  expect r20 == true, "Test 20 failed";

  print "All tests passed\n";
}