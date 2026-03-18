method RestoreThreeNumbers(x: seq<int>) returns (a: int, b: int, c: int)
{
  var maxVal := x[0];
  var i := 1;
  while i < |x|
  {
    if x[i] > maxVal {
      maxVal := x[i];
    }
    i := i + 1;
  }

  var result: seq<int> := [];
  i := 0;
  while i < |x|
  {
    if x[i] != maxVal {
      result := result + [maxVal - x[i]];
    }
    i := i + 1;
  }

  a := result[0];
  b := result[1];
  c := result[2];
}

method Main()
{
  // Test 1
  var a1, b1, c1 := RestoreThreeNumbers([3, 6, 5, 4]);
  expect a1 == 3, "Test 1 failed: a";
  expect b1 == 1, "Test 1 failed: b";
  expect c1 == 2, "Test 1 failed: c";

  // Test 2
  var a2, b2, c2 := RestoreThreeNumbers([40, 40, 40, 60]);
  expect a2 == 20, "Test 2 failed: a";
  expect b2 == 20, "Test 2 failed: b";
  expect c2 == 20, "Test 2 failed: c";

  // Test 3
  var a3, b3, c3 := RestoreThreeNumbers([201, 101, 101, 200]);
  expect a3 == 100, "Test 3 failed: a";
  expect b3 == 100, "Test 3 failed: b";
  expect c3 == 1, "Test 3 failed: c";

  // Test 4
  var a4, b4, c4 := RestoreThreeNumbers([1000000000, 666666667, 666666667, 666666666]);
  expect a4 == 333333333, "Test 4 failed: a";
  expect b4 == 333333333, "Test 4 failed: b";
  expect c4 == 333333334, "Test 4 failed: c";

  // Test 5
  var a5, b5, c5 := RestoreThreeNumbers([600000000, 900000000, 500000000, 1000000000]);
  expect a5 == 400000000, "Test 5 failed: a";
  expect b5 == 100000000, "Test 5 failed: b";
  expect c5 == 500000000, "Test 5 failed: c";

  // Test 6
  var a6, b6, c6 := RestoreThreeNumbers([2, 2, 3, 2]);
  expect a6 == 1, "Test 6 failed: a";
  expect b6 == 1, "Test 6 failed: b";
  expect c6 == 1, "Test 6 failed: c";

  // Test 7
  var a7, b7, c7 := RestoreThreeNumbers([10101000, 101000, 10001000, 10100000]);
  expect a7 == 10000000, "Test 7 failed: a";
  expect b7 == 100000, "Test 7 failed: b";
  expect c7 == 1000, "Test 7 failed: c";

  // Test 8
  var a8, b8, c8 := RestoreThreeNumbers([3, 999999990, 999999991, 999999992]);
  expect a8 == 999999989, "Test 8 failed: a";
  expect b8 == 2, "Test 8 failed: b";
  expect c8 == 1, "Test 8 failed: c";

  // Test 9
  var a9, b9, c9 := RestoreThreeNumbers([500000000, 500000001, 999999999, 1000000000]);
  expect a9 == 500000000, "Test 9 failed: a";
  expect b9 == 499999999, "Test 9 failed: b";
  expect c9 == 1, "Test 9 failed: c";

  print "All tests passed\n";
}