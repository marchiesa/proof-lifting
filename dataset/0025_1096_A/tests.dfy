predicate ValidPair(x: int, y: int, l: int, r: int)
{
  l <= x <= r && l <= y <= r && x != y && x > 0 && y % x == 0
}

method FindDivisible(l: int, r: int) returns (x: int, y: int)
  requires l >= 1
  requires 2 * l <= r
  ensures ValidPair(x, y, l, r)
{
  x := l;
  y := 2 * l;
}

method Main()
{
  var x: int, y: int;

  // ========== SPEC POSITIVE TESTS ==========
  // ValidPair(correct_x, correct_y, l, r) should be true

  // Test 1 sub-queries
  expect ValidPair(1, 2, 1, 10), "spec positive 1.1";
  expect ValidPair(3, 6, 3, 14), "spec positive 1.2";

  // Test 2
  expect ValidPair(6969, 13938, 6969, 696969), "spec positive 2";

  // Test 3
  expect ValidPair(696969, 1393938, 696969, 100000000), "spec positive 3";

  // Test 4
  expect ValidPair(69696969, 139393938, 69696969, 998244353), "spec positive 4";

  // Test 5
  expect ValidPair(1, 2, 1, 10), "spec positive 5";

  // Test 6 sub-queries
  expect ValidPair(1, 2, 1, 2), "spec positive 6.1";
  expect ValidPair(2, 4, 2, 6), "spec positive 6.2";
  expect ValidPair(3, 6, 3, 9), "spec positive 6.3";

  // Test 7 sub-queries
  expect ValidPair(1, 2, 1, 50), "spec positive 7.1";
  expect ValidPair(2, 4, 2, 4), "spec positive 7.2";
  expect ValidPair(3, 6, 3, 7), "spec positive 7.3";
  expect ValidPair(5, 10, 5, 15), "spec positive 7.4";
  expect ValidPair(10, 20, 10, 30), "spec positive 7.5";

  // Test 8
  expect ValidPair(2, 4, 2, 4), "spec positive 8";

  // Test 9 sub-queries
  expect ValidPair(1, 2, 1, 3), "spec positive 9.1";
  expect ValidPair(4, 8, 4, 8), "spec positive 9.2";

  // Test 10
  expect ValidPair(3, 6, 3, 9), "spec positive 10";

  // ========== SPEC NEGATIVE TESTS ==========
  // ValidPair(wrong_x, wrong_y, l, r) should be false

  // Neg 1: (1,10) -> wrong (2,2): x==y so invalid
  expect !ValidPair(2, 2, 1, 10), "spec negative 1";

  // Neg 2: (6969,696969) -> wrong (6970,13938): 13938 % 6970 != 0
  expect !ValidPair(6970, 13938, 6969, 696969), "spec negative 2";

  // Neg 3: (696969,100000000) -> wrong (696970,1393938): 1393938 % 696970 != 0
  expect !ValidPair(696970, 1393938, 696969, 100000000), "spec negative 3";

  // Neg 4: (69696969,998244353) -> wrong (69696970,139393938): 139393938 % 69696970 != 0
  expect !ValidPair(69696970, 139393938, 69696969, 998244353), "spec negative 4";

  // Neg 5: (1,10) -> wrong (2,2): x==y
  expect !ValidPair(2, 2, 1, 10), "spec negative 5";

  // Neg 6: (1,2) -> wrong (2,2): x==y
  expect !ValidPair(2, 2, 1, 2), "spec negative 6";

  // Neg 7: (1,50) -> wrong (2,2): x==y
  expect !ValidPair(2, 2, 1, 50), "spec negative 7";

  // Neg 8: (2,4) -> wrong (3,4): 4 % 3 != 0
  expect !ValidPair(3, 4, 2, 4), "spec negative 8";

  // Neg 9: (1,3) -> wrong (2,2): x==y
  expect !ValidPair(2, 2, 1, 3), "spec negative 9";

  // Neg 10: (3,9) -> wrong (4,6): 6 % 4 != 0
  expect !ValidPair(4, 6, 3, 9), "spec negative 10";

  // ========== IMPLEMENTATION TESTS ==========

  // Test 1
  x, y := FindDivisible(1, 10);
  expect x == 1 && y == 2, "impl test 1.1 failed";

  x, y := FindDivisible(3, 14);
  expect x == 3 && y == 6, "impl test 1.2 failed";

  // Test 2
  x, y := FindDivisible(6969, 696969);
  expect x == 6969 && y == 13938, "impl test 2 failed";

  // Test 3
  x, y := FindDivisible(696969, 100000000);
  expect x == 696969 && y == 1393938, "impl test 3 failed";

  // Test 4
  x, y := FindDivisible(69696969, 998244353);
  expect x == 69696969 && y == 139393938, "impl test 4 failed";

  // Test 5
  x, y := FindDivisible(1, 10);
  expect x == 1 && y == 2, "impl test 5 failed";

  // Test 6
  x, y := FindDivisible(1, 2);
  expect x == 1 && y == 2, "impl test 6.1 failed";

  x, y := FindDivisible(2, 6);
  expect x == 2 && y == 4, "impl test 6.2 failed";

  x, y := FindDivisible(3, 9);
  expect x == 3 && y == 6, "impl test 6.3 failed";

  // Test 7
  x, y := FindDivisible(1, 50);
  expect x == 1 && y == 2, "impl test 7.1 failed";

  x, y := FindDivisible(2, 4);
  expect x == 2 && y == 4, "impl test 7.2 failed";

  x, y := FindDivisible(3, 7);
  expect x == 3 && y == 6, "impl test 7.3 failed";

  x, y := FindDivisible(5, 15);
  expect x == 5 && y == 10, "impl test 7.4 failed";

  x, y := FindDivisible(10, 30);
  expect x == 10 && y == 20, "impl test 7.5 failed";

  // Test 8
  x, y := FindDivisible(2, 4);
  expect x == 2 && y == 4, "impl test 8 failed";

  // Test 9
  x, y := FindDivisible(1, 3);
  expect x == 1 && y == 2, "impl test 9.1 failed";

  x, y := FindDivisible(4, 8);
  expect x == 4 && y == 8, "impl test 9.2 failed";

  // Test 10
  x, y := FindDivisible(3, 9);
  expect x == 3 && y == 6, "impl test 10 failed";

  // Test 11
  x, y := FindDivisible(1, 5);
  expect x == 1 && y == 2, "impl test 11.1 failed";

  x, y := FindDivisible(2, 10);
  expect x == 2 && y == 4, "impl test 11.2 failed";

  x, y := FindDivisible(7, 14);
  expect x == 7 && y == 14, "impl test 11.3 failed";

  x, y := FindDivisible(20, 50);
  expect x == 20 && y == 40, "impl test 11.4 failed";

  // Test 12
  x, y := FindDivisible(1, 2);
  expect x == 1 && y == 2, "impl test 12 failed";

  // Test 13
  x, y := FindDivisible(5, 10);
  expect x == 5 && y == 10, "impl test 13.1 failed";

  x, y := FindDivisible(12, 36);
  expect x == 12 && y == 24, "impl test 13.2 failed";

  x, y := FindDivisible(1, 50);
  expect x == 1 && y == 2, "impl test 13.3 failed";

  // Test 14
  x, y := FindDivisible(25, 50);
  expect x == 25 && y == 50, "impl test 14.1 failed";

  x, y := FindDivisible(3, 6);
  expect x == 3 && y == 6, "impl test 14.2 failed";

  print "All tests passed\n";
}