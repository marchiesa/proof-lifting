method PrisonBreak(n: int, m: int, r: int, c: int) returns (time: int)
{
  var dr: int;
  if r - 1 > n - r { dr := r - 1; } else { dr := n - r; }
  var dc: int;
  if c - 1 > m - c { dc := c - 1; } else { dc := m - c; }
  time := dr + dc;
}

method Main()
{
  var result: int;

  // Test 1
  result := PrisonBreak(10, 10, 1, 1);
  expect result == 18, "PrisonBreak(10,10,1,1) failed";
  result := PrisonBreak(3, 5, 2, 4);
  expect result == 4, "PrisonBreak(3,5,2,4) failed";
  result := PrisonBreak(10, 2, 5, 1);
  expect result == 6, "PrisonBreak(10,2,5,1) failed";

  // Test 2
  result := PrisonBreak(1, 1, 1, 1);
  expect result == 0, "PrisonBreak(1,1,1,1) failed";

  // Test 3
  result := PrisonBreak(50, 50, 25, 25);
  expect result == 50, "PrisonBreak(50,50,25,25) failed";

  // Test 4
  result := PrisonBreak(2, 2, 1, 1);
  expect result == 2, "PrisonBreak(2,2,1,1) failed";
  result := PrisonBreak(3, 3, 2, 2);
  expect result == 2, "PrisonBreak(3,3,2,2) failed";
  result := PrisonBreak(4, 4, 1, 4);
  expect result == 6, "PrisonBreak(4,4,1,4) failed";
  result := PrisonBreak(5, 5, 5, 5);
  expect result == 8, "PrisonBreak(5,5,5,5) failed";

  // Test 5
  result := PrisonBreak(50, 50, 1, 1);
  expect result == 98, "PrisonBreak(50,50,1,1) failed";

  // Test 6
  result := PrisonBreak(7, 3, 4, 2);
  expect result == 4, "PrisonBreak(7,3,4,2) failed";
  result := PrisonBreak(1, 50, 1, 25);
  expect result == 25, "PrisonBreak(1,50,1,25) failed";
  result := PrisonBreak(50, 1, 25, 1);
  expect result == 25, "PrisonBreak(50,1,25,1) failed";
  result := PrisonBreak(6, 8, 6, 8);
  expect result == 12, "PrisonBreak(6,8,6,8) failed";

  // Test 7
  result := PrisonBreak(10, 10, 10, 10);
  expect result == 18, "PrisonBreak(10,10,10,10) failed";
  result := PrisonBreak(20, 30, 1, 30);
  expect result == 48, "PrisonBreak(20,30,1,30) failed";

  // Test 8
  result := PrisonBreak(2, 2, 1, 2);
  expect result == 2, "PrisonBreak(2,2,1,2) failed";
  result := PrisonBreak(2, 2, 2, 1);
  expect result == 2, "PrisonBreak(2,2,2,1) failed";
  result := PrisonBreak(2, 2, 2, 2);
  expect result == 2, "PrisonBreak(2,2,2,2) failed";
  result := PrisonBreak(3, 3, 1, 1);
  expect result == 4, "PrisonBreak(3,3,1,1) failed";

  // Test 9
  result := PrisonBreak(50, 50, 50, 50);
  expect result == 98, "PrisonBreak(50,50,50,50) failed";
  result := PrisonBreak(50, 50, 1, 50);
  expect result == 98, "PrisonBreak(50,50,1,50) failed";
  result := PrisonBreak(50, 50, 25, 1);
  expect result == 74, "PrisonBreak(50,50,25,1) failed";

  // Test 10
  result := PrisonBreak(5, 5, 3, 3);
  expect result == 4, "PrisonBreak(5,5,3,3) failed";
  result := PrisonBreak(4, 7, 2, 5);
  expect result == 6, "PrisonBreak(4,7,2,5) failed";
  result := PrisonBreak(8, 3, 1, 1);
  expect result == 9, "PrisonBreak(8,3,1,1) failed";
  result := PrisonBreak(6, 6, 6, 6);
  expect result == 10, "PrisonBreak(6,6,6,6) failed";
  result := PrisonBreak(10, 10, 5, 5);
  expect result == 10, "PrisonBreak(10,10,5,5) failed";
  result := PrisonBreak(3, 9, 2, 8);
  expect result == 8, "PrisonBreak(3,9,2,8) failed";
  result := PrisonBreak(7, 7, 4, 4);
  expect result == 6, "PrisonBreak(7,7,4,4) failed";
  result := PrisonBreak(2, 3, 1, 2);
  expect result == 2, "PrisonBreak(2,3,1,2) failed";
  result := PrisonBreak(15, 20, 8, 10);
  expect result == 17, "PrisonBreak(15,20,8,10) failed";

  print "All tests passed\n";
}