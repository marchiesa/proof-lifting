method ChessColoring(grids: seq<int>) returns (results: seq<int>)
{
  results := [];
  var i := 0;
  while i < |grids|
  {
    var x := grids[i];
    results := results + [x / 2 + 1];
    i := i + 1;
  }
}

method Main()
{
  // Test 1
  var r1 := ChessColoring([3, 4]);
  expect r1 == [2, 3], "Test 1 failed";

  // Test 2
  var r2 := ChessColoring([10000001]);
  expect r2 == [5000001], "Test 2 failed";

  // Test 3
  var r3 := ChessColoring([69]);
  expect r3 == [35], "Test 3 failed";

  // Test 4
  var r4 := ChessColoring([1]);
  expect r4 == [1], "Test 4 failed";

  // Test 5
  var r5 := ChessColoring([2]);
  expect r5 == [2], "Test 5 failed";

  // Test 6
  var r6 := ChessColoring([3]);
  expect r6 == [2], "Test 6 failed";

  // Test 7
  var r7 := ChessColoring([4]);
  expect r7 == [3], "Test 7 failed";

  // Test 8
  var r8 := ChessColoring([5]);
  expect r8 == [3], "Test 8 failed";

  // Test 9
  var r9 := ChessColoring([10]);
  expect r9 == [6], "Test 9 failed";

  // Test 10
  var r10 := ChessColoring([50]);
  expect r10 == [26], "Test 10 failed";

  // Test 11
  var r11 := ChessColoring([1, 2, 3]);
  expect r11 == [1, 2, 2], "Test 11 failed";

  // Test 12
  var r12 := ChessColoring([1, 2, 3, 4, 5]);
  expect r12 == [1, 2, 2, 3, 3], "Test 12 failed";

  // Test 13
  var r13 := ChessColoring([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
  expect r13 == [1, 2, 2, 3, 3, 4, 4, 5, 5, 6], "Test 13 failed";

  print "All tests passed\n";
}