method RedBlueShuffle(n: int, r: seq<int>, b: seq<int>) returns (result: string)
{
  var x := 0;
  var y := 0;
  var i := 0;
  while i < n
  {
    if r[i] > b[i] {
      x := x + 1;
    } else if r[i] < b[i] {
      y := y + 1;
    }
    i := i + 1;
  }
  if x > y {
    result := "RED";
  } else if x < y {
    result := "BLUE";
  } else {
    result := "EQUAL";
  }
}

method Main()
{
  // Test 1 (t=3)
  var r1 := RedBlueShuffle(3, [7, 7, 7], [1, 1, 1]);
  expect r1 == "RED", "Test 1.1 failed";

  var r2 := RedBlueShuffle(3, [3, 1, 4], [1, 5, 9]);
  expect r2 == "BLUE", "Test 1.2 failed";

  var r3 := RedBlueShuffle(5, [0, 9, 2, 8, 1], [0, 9, 2, 8, 1]);
  expect r3 == "EQUAL", "Test 1.3 failed";

  // Test 2 (t=1)
  var r4 := RedBlueShuffle(1, [5], [3]);
  expect r4 == "RED", "Test 2 failed";

  // Test 3 (t=1)
  var r5 := RedBlueShuffle(2, [0, 0], [0, 0]);
  expect r5 == "EQUAL", "Test 3 failed";

  // Test 4 (t=1)
  var r6 := RedBlueShuffle(3, [1, 2, 3], [4, 5, 6]);
  expect r6 == "BLUE", "Test 4 failed";

  // Test 5 (t=1)
  var r7 := RedBlueShuffle(4, [1, 1, 1, 1], [2, 2, 2, 2]);
  expect r7 == "BLUE", "Test 5 failed";

  // Test 6 (t=1)
  var r8 := RedBlueShuffle(5, [9, 9, 9, 9, 9], [0, 0, 0, 0, 0]);
  expect r8 == "RED", "Test 6 failed";

  // Test 7 (t=1)
  var r9 := RedBlueShuffle(3, [3, 1, 4], [1, 5, 9]);
  expect r9 == "BLUE", "Test 7 failed";

  // Test 8 (t=1)
  var r10 := RedBlueShuffle(6, [0, 1, 2, 3, 4, 5], [5, 4, 3, 2, 1, 0]);
  expect r10 == "EQUAL", "Test 8 failed";

  // Test 9 (t=1)
  var r11 := RedBlueShuffle(5, [0, 9, 2, 8, 1], [0, 9, 2, 8, 1]);
  expect r11 == "EQUAL", "Test 9 failed";

  // Test 10 (t=1)
  var r12 := RedBlueShuffle(7, [1, 2, 3, 4, 5, 6, 7], [7, 6, 5, 4, 3, 2, 1]);
  expect r12 == "EQUAL", "Test 10 failed";

  // Test 11 (t=2)
  var r13 := RedBlueShuffle(3, [7, 7, 7], [1, 1, 1]);
  expect r13 == "RED", "Test 11.1 failed";

  var r14 := RedBlueShuffle(4, [0, 0, 0, 0], [0, 0, 0, 0]);
  expect r14 == "EQUAL", "Test 11.2 failed";

  print "All tests passed\n";
}