method GameShopping(c: seq<int>, a: seq<int>) returns (count: int)
{
  count := 0;
  var i := 0;
  var j := 0;
  while i < |c| && j < |a|
  {
    if a[j] >= c[i] {
      count := count + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  // Test 1
  var r1 := GameShopping([2, 4, 5, 2, 4], [5, 3, 4, 6]);
  expect r1 == 3, "Test 1 failed";

  // Test 2
  var r2 := GameShopping([20, 40, 50, 20, 40], [19, 20]);
  expect r2 == 0, "Test 2 failed";

  // Test 3
  var r3 := GameShopping([4, 8, 15, 16, 23, 42], [1000, 1000, 1000, 1000]);
  expect r3 == 4, "Test 3 failed";

  // Test 4
  var r4 := GameShopping([1, 1, 1, 1, 1], [5]);
  expect r4 == 1, "Test 4 failed";

  // Test 5
  var r5 := GameShopping([10, 1, 1, 1, 1], [1000]);
  expect r5 == 1, "Test 5 failed";

  // Test 6
  var r6 := GameShopping([100, 100, 100, 100, 100], [100]);
  expect r6 == 1, "Test 6 failed";

  // Test 7
  var r7 := GameShopping([2, 1], [1]);
  expect r7 == 1, "Test 7 failed";

  // Test 8
  var r8 := GameShopping([3, 1], [2, 4, 2]);
  expect r8 == 1, "Test 8 failed";

  // Test 9
  var r9 := GameShopping([4], [1, 4, 3, 3, 2]);
  expect r9 == 0, "Test 9 failed";

  // Test 10
  var r10 := GameShopping([4, 2, 3, 1, 1], [2, 1, 3]);
  expect r10 == 3, "Test 10 failed";

  // Test 11
  var r11 := GameShopping([5, 2, 5], [1, 4, 1, 4, 2]);
  expect r11 == 0, "Test 11 failed";

  // Test 12
  var r12 := GameShopping([9, 7, 10, 2, 1, 1, 1], [8, 9, 6]);
  expect r12 == 3, "Test 12 failed";

  // Test 13
  var r13 := GameShopping([2, 5, 3, 3, 2], [2, 5, 3]);
  expect r13 == 3, "Test 13 failed";

  print "All tests passed\n";
}