method PensAndPencils(a: int, b: int, c: int, d: int, k: int) returns (x: int, y: int)
{
  var pens := (a + c - 1) / c;
  var pencils := (b + d - 1) / d;
  if pens + pencils <= k {
    return pens, pencils;
  } else {
    return -1, 0;
  }
}

method Main()
{
  var x: int, y: int;

  // Test 1.1
  x, y := PensAndPencils(7, 5, 4, 5, 8);
  expect x == 2 && y == 1, "Test 1.1 failed";

  // Test 1.2
  x, y := PensAndPencils(7, 5, 4, 5, 2);
  expect x == -1, "Test 1.2 failed";

  // Test 1.3
  x, y := PensAndPencils(20, 53, 45, 26, 4);
  expect x == 1 && y == 3, "Test 1.3 failed";

  // Test 2.1
  x, y := PensAndPencils(80, 72, 20, 12, 10);
  expect x == 4 && y == 6, "Test 2.1 failed";

  // Test 2.2
  x, y := PensAndPencils(81, 72, 20, 12, 11);
  expect x == 5 && y == 6, "Test 2.2 failed";

  // Test 2.3
  x, y := PensAndPencils(80, 73, 20, 12, 11);
  expect x == 4 && y == 7, "Test 2.3 failed";

  // Test 2.4
  x, y := PensAndPencils(81, 73, 20, 12, 12);
  expect x == 5 && y == 7, "Test 2.4 failed";

  // Test 2.5
  x, y := PensAndPencils(80, 73, 20, 12, 10);
  expect x == -1, "Test 2.5 failed";

  // Test 2.6
  x, y := PensAndPencils(3, 99, 5, 1, 100);
  expect x == 1 && y == 99, "Test 2.6 failed";

  // Test 2.7
  x, y := PensAndPencils(99, 1, 1, 4, 100);
  expect x == 99 && y == 1, "Test 2.7 failed";

  // Test 2.8
  x, y := PensAndPencils(53, 37, 13, 3, 17);
  expect x == -1, "Test 2.8 failed";

  // Test 3
  x, y := PensAndPencils(2, 5, 4, 2, 2);
  expect x == -1, "Test 3 failed";

  // Test 4
  x, y := PensAndPencils(5, 4, 6, 1, 5);
  expect x == 1 && y == 4, "Test 4 failed";

  // Test 5
  x, y := PensAndPencils(2, 2, 2, 3, 2);
  expect x == 1 && y == 1, "Test 5 failed";

  // Test 6
  x, y := PensAndPencils(1, 6, 3, 2, 3);
  expect x == -1, "Test 6 failed";

  // Test 7
  x, y := PensAndPencils(1, 1, 6, 7, 2);
  expect x == 1 && y == 1, "Test 7 failed";

  // Test 8
  x, y := PensAndPencils(1, 1, 1, 7, 2);
  expect x == 1 && y == 1, "Test 8 failed";

  // Test 9
  x, y := PensAndPencils(1, 2, 5, 2, 2);
  expect x == 1 && y == 1, "Test 9 failed";

  // Test 10
  x, y := PensAndPencils(3, 99, 5, 1, 100);
  expect x == 1 && y == 99, "Test 10 failed";

  // Test 11
  x, y := PensAndPencils(7, 4, 5, 1, 5);
  expect x == -1, "Test 11 failed";

  // Test 12
  x, y := PensAndPencils(99, 1, 1, 4, 100);
  expect x == 99 && y == 1, "Test 12 failed";

  // Test 13
  x, y := PensAndPencils(99, 6, 1, 8, 100);
  expect x == 99 && y == 1, "Test 13 failed";

  // Test 14
  x, y := PensAndPencils(7, 2, 3, 2, 3);
  expect x == -1, "Test 14 failed";

  // Test 15
  x, y := PensAndPencils(3, 99, 6, 1, 100);
  expect x == 1 && y == 99, "Test 15 failed";

  // Test 16
  x, y := PensAndPencils(4, 1, 7, 1, 2);
  expect x == 1 && y == 1, "Test 16 failed";

  // Test 17
  x, y := PensAndPencils(1, 1, 1, 6, 2);
  expect x == 1 && y == 1, "Test 17 failed";

  // Test 18
  x, y := PensAndPencils(2, 1, 3, 8, 2);
  expect x == 1 && y == 1, "Test 18 failed";

  // Test 19
  x, y := PensAndPencils(3, 1, 3, 1, 7);
  expect x == 1 && y == 1, "Test 19 failed";

  // Test 20
  x, y := PensAndPencils(1, 1, 1, 1, 2);
  expect x == 1 && y == 1, "Test 20 failed";

  print "All tests passed\n";
}