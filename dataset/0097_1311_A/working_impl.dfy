method AddOddOrSubtractEven(a: int, b: int) returns (moves: int)
{
  if a == b {
    moves := 0;
  } else if a % 2 == b % 2 && a > b {
    moves := 1;
  } else if a % 2 != b % 2 && b > a {
    moves := 1;
  } else {
    moves := 2;
  }
}

method Main()
{
  var result: int;

  // Test 1
  result := AddOddOrSubtractEven(2, 3);
  expect result == 1, "Test (2,3) failed";

  result := AddOddOrSubtractEven(10, 10);
  expect result == 0, "Test (10,10) failed";

  result := AddOddOrSubtractEven(2, 4);
  expect result == 2, "Test (2,4) failed";

  result := AddOddOrSubtractEven(7, 4);
  expect result == 2, "Test (7,4) failed";

  result := AddOddOrSubtractEven(9, 3);
  expect result == 1, "Test (9,3) failed";

  // Test 2
  result := AddOddOrSubtractEven(19260817, 114514);
  expect result == 2, "Test (19260817,114514) failed";

  // Test 3
  result := AddOddOrSubtractEven(484887, 54);
  expect result == 2, "Test (484887,54) failed";

  // Test 4
  result := AddOddOrSubtractEven(55678978, 55678978);
  expect result == 0, "Test (55678978,55678978) failed";

  // Test 5
  result := AddOddOrSubtractEven(1, 2);
  expect result == 1, "Test (1,2) failed";

  // Test 6
  result := AddOddOrSubtractEven(5, 5);
  expect result == 0, "Test (5,5) failed";

  // Test 7
  result := AddOddOrSubtractEven(3, 7);
  expect result == 2, "Test (3,7) failed";

  // Test 8
  result := AddOddOrSubtractEven(10, 4);
  expect result == 1, "Test (10,4) failed";

  // Test 9
  result := AddOddOrSubtractEven(1, 50);
  expect result == 1, "Test (1,50) failed";

  // Test 10 (subset of Test 1, included for completeness)
  result := AddOddOrSubtractEven(2, 3);
  expect result == 1, "Test 10 (2,3) failed";

  result := AddOddOrSubtractEven(10, 10);
  expect result == 0, "Test 10 (10,10) failed";

  result := AddOddOrSubtractEven(7, 4);
  expect result == 2, "Test 10 (7,4) failed";

  // Test 11
  result := AddOddOrSubtractEven(49, 50);
  expect result == 1, "Test (49,50) failed";

  result := AddOddOrSubtractEven(1, 1);
  expect result == 0, "Test (1,1) failed";

  // Test 12
  result := AddOddOrSubtractEven(1, 1);
  expect result == 0, "Test 12 (1,1) failed";

  result := AddOddOrSubtractEven(2, 2);
  expect result == 0, "Test (2,2) failed";

  result := AddOddOrSubtractEven(3, 3);
  expect result == 0, "Test (3,3) failed";

  result := AddOddOrSubtractEven(4, 4);
  expect result == 0, "Test (4,4) failed";

  // Test 13
  result := AddOddOrSubtractEven(25, 13);
  expect result == 1, "Test (25,13) failed";

  // Test 14
  result := AddOddOrSubtractEven(1, 3);
  expect result == 2, "Test (1,3) failed";

  result := AddOddOrSubtractEven(4, 2);
  expect result == 1, "Test (4,2) failed";

  result := AddOddOrSubtractEven(7, 8);
  expect result == 1, "Test (7,8) failed";

  result := AddOddOrSubtractEven(50, 1);
  expect result == 2, "Test (50,1) failed";

  result := AddOddOrSubtractEven(33, 47);
  expect result == 2, "Test (33,47) failed";

  print "All tests passed\n";
}