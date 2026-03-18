predicate CanReach(x: int, y: int, n: int, m: int, cost: int)
  requires 1 <= x <= n && 1 <= y <= m
  decreases (n - x) + (m - y)
{
  (x == n && y == m && cost == 0)
  ||
  (y < m && CanReach(x, y + 1, n, m, cost - x))
  ||
  (x < n && CanReach(x + 1, y, n, m, cost - y))
}

method {:verify false} TheCakeIsALie(n: int, m: int, k: int) returns (result: bool)
  requires n >= 1 && m >= 1
  ensures result == CanReach(1, 1, n, m, k)
{
  var remaining := k - (1 * (m - 1) + m * (n - 1));
  result := remaining == 0;
}

method Main()
{
  var r: bool;
  var b: bool;

  // ===== SPEC POSITIVE TESTS =====
  // Only small inputs where recursive CanReach is feasible at runtime.

  // Test 3: (1,1,0) -> YES
  b := CanReach(1, 1, 1, 1, 0);
  expect b == true, "spec positive 1";

  // Test 4: (2,2,2) -> NO
  b := CanReach(1, 1, 2, 2, 2);
  expect b == false, "spec positive 2";

  // Test 1 case: (2,2,3) -> YES
  b := CanReach(1, 1, 2, 2, 3);
  expect b == true, "spec positive 3";

  // Test 1 case: (2,2,4) -> NO
  b := CanReach(1, 1, 2, 2, 4);
  expect b == false, "spec positive 4";

  // Test 1 case: (1,4,3) -> YES
  b := CanReach(1, 1, 1, 4, 3);
  expect b == true, "spec positive 5";

  // Test 5: (1,5,4) -> YES
  b := CanReach(1, 1, 1, 5, 4);
  expect b == true, "spec positive 6";

  // Test 6: (5,1,4) -> YES
  b := CanReach(1, 1, 5, 1, 4);
  expect b == true, "spec positive 7";

  // Test 7: (3,3,8) -> YES
  b := CanReach(1, 1, 3, 3, 8);
  expect b == true, "spec positive 8";

  // Test 9: (1,1,5) -> NO
  b := CanReach(1, 1, 1, 1, 5);
  expect b == false, "spec positive 9";

  // Test 2 case: (3,3,7) -> NO
  b := CanReach(1, 1, 3, 3, 7);
  expect b == false, "spec positive 10";

  // Test 2 case: (3,3,9) -> NO
  b := CanReach(1, 1, 3, 3, 9);
  expect b == false, "spec positive 11";

  // Test 2 case: (2,4,8) -> NO
  b := CanReach(1, 1, 2, 4, 8);
  expect b == false, "spec positive 12";

  // Test 11 case: (2,3,5) -> YES
  b := CanReach(1, 1, 2, 3, 5);
  expect b == true, "spec positive 13";

  // Test 12 case: (3,2,4) -> NO
  b := CanReach(1, 1, 3, 2, 4);
  expect b == false, "spec positive 14";

  // Test 12 case: (1,1,1) -> NO
  b := CanReach(1, 1, 1, 1, 1);
  expect b == false, "spec positive 15";

  // Test 12 case: (7,3,12) -> NO
  b := CanReach(1, 1, 7, 3, 12);
  expect b == false, "spec positive 16";

  // Test 12 case: (2,8,9) -> NO
  b := CanReach(1, 1, 2, 8, 9);
  expect b == false, "spec positive 17";

  // Test 11 case: (4,4,12) -> NO
  b := CanReach(1, 1, 4, 4, 12);
  expect b == false, "spec positive 18";

  // Test 12 case: (5,5,40) -> NO
  b := CanReach(1, 1, 5, 5, 40);
  expect b == false, "spec positive 19";

  // ===== SPEC NEGATIVE TESTS =====
  // Test that spec rejects wrong outputs. Small inputs only.

  // Neg 3: (1,1,0) correct=true, wrong=false
  b := CanReach(1, 1, 1, 1, 0);
  expect !(b == false), "spec negative 3";

  // Neg 4: (2,2,2) correct=false, wrong=true
  b := CanReach(1, 1, 2, 2, 2);
  expect !(b == true), "spec negative 4";

  // Neg 5: (1,5,4) correct=true, wrong=false
  b := CanReach(1, 1, 1, 5, 4);
  expect !(b == false), "spec negative 5";

  // Neg 6: (5,1,4) correct=true, wrong=false
  b := CanReach(1, 1, 5, 1, 4);
  expect !(b == false), "spec negative 6";

  // Neg 7: (3,3,8) correct=true, wrong=false
  b := CanReach(1, 1, 3, 3, 8);
  expect !(b == false), "spec negative 7";

  // Neg 9: (1,1,5) correct=false, wrong=true
  b := CanReach(1, 1, 1, 1, 5);
  expect !(b == true), "spec negative 9";

  // ===== IMPLEMENTATION TESTS =====
  // Full-size inputs are fine here since the method is O(1).

  // Test 1
  r := TheCakeIsALie(1, 1, 0);
  expect r == true, "impl test 1a";
  r := TheCakeIsALie(2, 2, 2);
  expect r == false, "impl test 1b";
  r := TheCakeIsALie(2, 2, 3);
  expect r == true, "impl test 1c";
  r := TheCakeIsALie(2, 2, 4);
  expect r == false, "impl test 1d";
  r := TheCakeIsALie(1, 4, 3);
  expect r == true, "impl test 1e";
  r := TheCakeIsALie(100, 100, 10000);
  expect r == false, "impl test 1f";

  // Test 2
  r := TheCakeIsALie(3, 3, 7);
  expect r == false, "impl test 2a";
  r := TheCakeIsALie(3, 3, 9);
  expect r == false, "impl test 2b";
  r := TheCakeIsALie(2, 4, 8);
  expect r == false, "impl test 2c";

  // Test 3
  r := TheCakeIsALie(1, 1, 0);
  expect r == true, "impl test 3";

  // Test 4
  r := TheCakeIsALie(2, 2, 2);
  expect r == false, "impl test 4";

  // Test 5
  r := TheCakeIsALie(1, 5, 4);
  expect r == true, "impl test 5";

  // Test 6
  r := TheCakeIsALie(5, 1, 4);
  expect r == true, "impl test 6";

  // Test 7
  r := TheCakeIsALie(3, 3, 8);
  expect r == true, "impl test 7";

  // Test 8
  r := TheCakeIsALie(10, 10, 100);
  expect r == false, "impl test 8";

  // Test 9
  r := TheCakeIsALie(1, 1, 5);
  expect r == false, "impl test 9";

  // Test 10
  r := TheCakeIsALie(50, 50, 2500);
  expect r == false, "impl test 10";

  // Test 11
  r := TheCakeIsALie(2, 3, 5);
  expect r == true, "impl test 11a";
  r := TheCakeIsALie(4, 4, 12);
  expect r == false, "impl test 11b";
  r := TheCakeIsALie(1, 10, 9);
  expect r == true, "impl test 11c";

  // Test 12
  r := TheCakeIsALie(3, 2, 4);
  expect r == false, "impl test 12a";
  r := TheCakeIsALie(5, 5, 40);
  expect r == false, "impl test 12b";
  r := TheCakeIsALie(1, 1, 1);
  expect r == false, "impl test 12c";
  r := TheCakeIsALie(7, 3, 12);
  expect r == false, "impl test 12d";
  r := TheCakeIsALie(2, 8, 9);
  expect r == false, "impl test 12e";

  print "All tests passed\n";
}