method Fence(a: int, b: int, c: int) returns (d: int)
{
  d := a + b + c - 1;
}

method Main()
{
  // Test 1
  var d1 := Fence(1, 2, 3);
  expect d1 == 5, "Test 1a failed";

  var d2 := Fence(12, 34, 56);
  expect d2 == 101, "Test 1b failed";

  // Test 2
  var d3 := Fence(2434, 2442, 14);
  expect d3 == 4889, "Test 2 failed";

  // Test 3
  var d4 := Fence(10, 20, 10);
  expect d4 == 39, "Test 3 failed";

  // Test 4
  var d5 := Fence(3, 4, 5);
  expect d5 == 11, "Test 4 failed";

  // Test 5
  var d6 := Fence(2, 1, 2);
  expect d6 == 4, "Test 5 failed";

  // Test 6
  var d7 := Fence(5, 4, 3);
  expect d7 == 11, "Test 6 failed";

  print "All tests passed\n";
}