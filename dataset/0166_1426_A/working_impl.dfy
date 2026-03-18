method FloorNumber(n: int, x: int) returns (floor: int)
{
  if n <= 2 {
    floor := 1;
  } else {
    var m := n - 3;
    floor := m / x + 2;
  }
}

method Main()
{
  var result: int;

  // Test 1 / Test 2 / Test 9 share some cases
  result := FloorNumber(7, 3);
  expect result == 3, "FloorNumber(7, 3) failed";

  result := FloorNumber(1, 5);
  expect result == 1, "FloorNumber(1, 5) failed";

  result := FloorNumber(22, 5);
  expect result == 5, "FloorNumber(22, 5) failed";

  result := FloorNumber(987, 13);
  expect result == 77, "FloorNumber(987, 13) failed";

  // Test 3
  result := FloorNumber(1, 1);
  expect result == 1, "FloorNumber(1, 1) failed";

  result := FloorNumber(2, 1);
  expect result == 1, "FloorNumber(2, 1) failed";

  result := FloorNumber(3, 1);
  expect result == 2, "FloorNumber(3, 1) failed";

  // Test 4
  result := FloorNumber(5, 3);
  expect result == 2, "FloorNumber(5, 3) failed";

  // Test 5
  result := FloorNumber(10, 4);
  expect result == 3, "FloorNumber(10, 4) failed";

  result := FloorNumber(15, 5);
  expect result == 4, "FloorNumber(15, 5) failed";

  // Test 6
  result := FloorNumber(1, 10);
  expect result == 1, "FloorNumber(1, 10) failed";

  // Test 7
  result := FloorNumber(2, 7);
  expect result == 1, "FloorNumber(2, 7) failed";

  // Test 8
  result := FloorNumber(3, 2);
  expect result == 2, "FloorNumber(3, 2) failed";

  // Test 9 (additional cases)
  result := FloorNumber(50, 10);
  expect result == 6, "FloorNumber(50, 10) failed";

  result := FloorNumber(4, 2);
  expect result == 2, "FloorNumber(4, 2) failed";

  // Test 10
  result := FloorNumber(11, 3);
  expect result == 4, "FloorNumber(11, 3) failed";

  // Test 11
  result := FloorNumber(6, 2);
  expect result == 3, "FloorNumber(6, 2) failed";

  result := FloorNumber(8, 2);
  expect result == 4, "FloorNumber(8, 2) failed";

  result := FloorNumber(10, 2);
  expect result == 5, "FloorNumber(10, 2) failed";

  // Test 12
  result := FloorNumber(49, 7);
  expect result == 8, "FloorNumber(49, 7) failed";

  result := FloorNumber(25, 6);
  expect result == 5, "FloorNumber(25, 6) failed";

  result := FloorNumber(2, 9);
  expect result == 1, "FloorNumber(2, 9) failed";

  result := FloorNumber(30, 4);
  expect result == 8, "FloorNumber(30, 4) failed";

  print "All tests passed\n";
}