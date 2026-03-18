method FindDivisible(l: int, r: int) returns (x: int, y: int)
{
  x := l;
  y := 2 * l;
}

method Main()
{
  var x: int, y: int;

  // Test 1
  x, y := FindDivisible(1, 10);
  expect x == 1 && y == 2, "Test 1.1 failed";

  x, y := FindDivisible(3, 14);
  expect x == 3 && y == 6, "Test 1.2 failed";

  x, y := FindDivisible(1, 10);
  expect x == 1 && y == 2, "Test 1.3 failed";

  // Test 2
  x, y := FindDivisible(6969, 696969);
  expect x == 6969 && y == 13938, "Test 2.1 failed";

  x, y := FindDivisible(6969, 696969);
  expect x == 6969 && y == 13938, "Test 2.2 failed";

  x, y := FindDivisible(6969, 696969);
  expect x == 6969 && y == 13938, "Test 2.3 failed";

  // Test 3
  x, y := FindDivisible(696969, 100000000);
  expect x == 696969 && y == 1393938, "Test 3 failed";

  // Test 4
  x, y := FindDivisible(69696969, 998244353);
  expect x == 69696969 && y == 139393938, "Test 4 failed";

  // Test 5
  x, y := FindDivisible(1, 10);
  expect x == 1 && y == 2, "Test 5 failed";

  // Test 6
  x, y := FindDivisible(1, 2);
  expect x == 1 && y == 2, "Test 6.1 failed";

  x, y := FindDivisible(2, 6);
  expect x == 2 && y == 4, "Test 6.2 failed";

  x, y := FindDivisible(3, 9);
  expect x == 3 && y == 6, "Test 6.3 failed";

  // Test 7
  x, y := FindDivisible(1, 50);
  expect x == 1 && y == 2, "Test 7.1 failed";

  x, y := FindDivisible(2, 4);
  expect x == 2 && y == 4, "Test 7.2 failed";

  x, y := FindDivisible(3, 7);
  expect x == 3 && y == 6, "Test 7.3 failed";

  x, y := FindDivisible(5, 15);
  expect x == 5 && y == 10, "Test 7.4 failed";

  x, y := FindDivisible(10, 30);
  expect x == 10 && y == 20, "Test 7.5 failed";

  // Test 8
  x, y := FindDivisible(2, 4);
  expect x == 2 && y == 4, "Test 8 failed";

  // Test 9
  x, y := FindDivisible(1, 3);
  expect x == 1 && y == 2, "Test 9.1 failed";

  x, y := FindDivisible(4, 8);
  expect x == 4 && y == 8, "Test 9.2 failed";

  // Test 10
  x, y := FindDivisible(3, 9);
  expect x == 3 && y == 6, "Test 10 failed";

  // Test 11
  x, y := FindDivisible(1, 5);
  expect x == 1 && y == 2, "Test 11.1 failed";

  x, y := FindDivisible(2, 10);
  expect x == 2 && y == 4, "Test 11.2 failed";

  x, y := FindDivisible(7, 14);
  expect x == 7 && y == 14, "Test 11.3 failed";

  x, y := FindDivisible(20, 50);
  expect x == 20 && y == 40, "Test 11.4 failed";

  // Test 12
  x, y := FindDivisible(1, 2);
  expect x == 1 && y == 2, "Test 12 failed";

  // Test 13
  x, y := FindDivisible(5, 10);
  expect x == 5 && y == 10, "Test 13.1 failed";

  x, y := FindDivisible(12, 36);
  expect x == 12 && y == 24, "Test 13.2 failed";

  x, y := FindDivisible(1, 50);
  expect x == 1 && y == 2, "Test 13.3 failed";

  // Test 14
  x, y := FindDivisible(25, 50);
  expect x == 25 && y == 50, "Test 14.1 failed";

  x, y := FindDivisible(3, 6);
  expect x == 3 && y == 6, "Test 14.2 failed";

  print "All tests passed\n";
}