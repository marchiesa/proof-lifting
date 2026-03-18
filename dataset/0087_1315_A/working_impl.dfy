method DeadPixel(a: int, b: int, x: int, y: int) returns (area: int)
{
  var v1 := x * b;
  var v2 := y * a;
  var v3 := (a - x - 1) * b;
  var v4 := (b - y - 1) * a;
  area := v1;
  if v2 > area { area := v2; }
  if v3 > area { area := v3; }
  if v4 > area { area := v4; }
  return;
}

method Main()
{
  var result: int;

  // Test 1
  result := DeadPixel(8, 8, 0, 0);
  expect result == 56, "Test 1.1 failed";
  result := DeadPixel(1, 10, 0, 3);
  expect result == 6, "Test 1.2 failed";
  result := DeadPixel(17, 31, 10, 4);
  expect result == 442, "Test 1.3 failed";
  result := DeadPixel(2, 1, 0, 0);
  expect result == 1, "Test 1.4 failed";
  result := DeadPixel(5, 10, 3, 9);
  expect result == 45, "Test 1.5 failed";
  result := DeadPixel(10, 10, 4, 8);
  expect result == 80, "Test 1.6 failed";

  // Test 2
  result := DeadPixel(10, 10, 5, 5);
  expect result == 50, "Test 2.1 failed";
  result := DeadPixel(1, 2, 0, 0);
  expect result == 1, "Test 2.2 failed";
  result := DeadPixel(50, 50, 25, 25);
  expect result == 1250, "Test 2.3 failed";

  // Test 3
  result := DeadPixel(1, 2, 0, 0);
  expect result == 1, "Test 3.1 failed";

  // Test 4
  result := DeadPixel(3, 3, 1, 1);
  expect result == 3, "Test 4.1 failed";
  result := DeadPixel(4, 4, 0, 0);
  expect result == 12, "Test 4.2 failed";

  // Test 5
  result := DeadPixel(50, 50, 49, 49);
  expect result == 2450, "Test 5.1 failed";

  // Test 6
  result := DeadPixel(2, 2, 0, 0);
  expect result == 2, "Test 6.1 failed";
  result := DeadPixel(2, 2, 1, 1);
  expect result == 2, "Test 6.2 failed";
  result := DeadPixel(2, 2, 0, 1);
  expect result == 2, "Test 6.3 failed";
  result := DeadPixel(2, 2, 1, 0);
  expect result == 2, "Test 6.4 failed";

  // Test 7
  result := DeadPixel(1, 50, 0, 25);
  expect result == 25, "Test 7.1 failed";

  // Test 8
  result := DeadPixel(50, 1, 25, 0);
  expect result == 25, "Test 8.1 failed";
  result := DeadPixel(10, 10, 0, 9);
  expect result == 90, "Test 8.2 failed";
  result := DeadPixel(10, 10, 9, 0);
  expect result == 90, "Test 8.3 failed";

  // Test 9
  result := DeadPixel(7, 3, 3, 1);
  expect result == 9, "Test 9.1 failed";
  result := DeadPixel(5, 5, 2, 2);
  expect result == 10, "Test 9.2 failed";

  // Test 10
  result := DeadPixel(3, 7, 1, 3);
  expect result == 9, "Test 10.1 failed";
  result := DeadPixel(6, 4, 5, 3);
  expect result == 20, "Test 10.2 failed";
  result := DeadPixel(8, 2, 7, 1);
  expect result == 14, "Test 10.3 failed";
  result := DeadPixel(4, 9, 0, 4);
  expect result == 27, "Test 10.4 failed";
  result := DeadPixel(9, 3, 4, 0);
  expect result == 18, "Test 10.5 failed";

  // Test 11
  result := DeadPixel(10, 10, 5, 0);
  expect result == 90, "Test 11.1 failed";

  print "All tests passed\n";
}