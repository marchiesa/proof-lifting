method RequiredRemainder(x: int, y: int, n: int) returns (k: int)
{
  var p := n % x;
  if p == y {
    k := n;
  } else if p > y {
    k := n - p + y;
  } else {
    k := n - p - (x - y);
  }
}

method Main()
{
  var result: int;

  // Test 1 cases
  result := RequiredRemainder(7, 5, 12345);
  expect result == 12339, "Test 1.1 failed";

  result := RequiredRemainder(5, 0, 4);
  expect result == 0, "Test 1.2 failed";

  result := RequiredRemainder(10, 5, 15);
  expect result == 15, "Test 1.3 failed";

  result := RequiredRemainder(17, 8, 54321);
  expect result == 54306, "Test 1.4 failed";

  result := RequiredRemainder(499999993, 9, 1000000000);
  expect result == 999999995, "Test 1.5 failed";

  result := RequiredRemainder(10, 5, 187);
  expect result == 185, "Test 1.6 failed";

  result := RequiredRemainder(2, 0, 999999999);
  expect result == 999999998, "Test 1.7 failed";

  // Test 2
  result := RequiredRemainder(1000000000, 0, 999999999);
  expect result == 0, "Test 2 failed";

  // Test 3
  result := RequiredRemainder(43284, 1, 33424242);
  expect result == 33415249, "Test 3 failed";

  // Test 4
  result := RequiredRemainder(31, 2, 104);
  expect result == 95, "Test 4 failed";

  // Test 5
  result := RequiredRemainder(943643, 1, 23522222);
  expect result == 22647433, "Test 5 failed";

  // Test 6
  result := RequiredRemainder(4452384, 1, 3573842);
  expect result == 1, "Test 6 failed";

  // Test 7
  result := RequiredRemainder(33, 6, 100);
  expect result == 72, "Test 7 failed";

  print "All tests passed\n";
}