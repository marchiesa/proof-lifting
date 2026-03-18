predicate Exceeds(a: int, b: int, n: int) {
  a > n || b > n
}

predicate Reachable(a: int, b: int, n: int, steps: nat)
  decreases steps
{
  Exceeds(a, b, n) ||
  (steps > 0 && (Reachable(a + b, b, n, steps - 1) || Reachable(a, b + a, n, steps - 1)))
}

method CPlusEqual(a: int, b: int, n: int) returns (ops: int)
  requires a > 0 && b > 0 && n > 0
  requires a <= n && b <= n
  ensures ops >= 1 && Reachable(a, b, n, ops) && !Reachable(a, b, n, ops - 1)
{
  var x := a;
  var y := b;
  if x > y {
    x, y := y, x;
  }
  var i := 1;
  while i < 1000 {
    if i % 2 == 1 {
      x := x + y;
    } else {
      y := y + x;
    }
    if x > n || y > n {
      ops := i;
      return;
    }
    i := i + 1;
  }
  ops := 0;
  return;
}

method Main()
{
  var result: int;

  // ============ SPEC POSITIVE TESTS ============
  // ensures: ops >= 1 && Reachable(a, b, n, ops) && !Reachable(a, b, n, ops - 1)
  // Using cases with small ops to keep Reachable evaluation tractable

  // (1,1,1) → 1
  expect 1 >= 1 && Reachable(1, 1, 1, 1) && !Reachable(1, 1, 1, 0), "spec positive 1";
  // (1,2,3) → 2
  expect 2 >= 1 && Reachable(1, 2, 3, 2) && !Reachable(1, 2, 3, 1), "spec positive 2";
  // (3,4,7) → 2
  expect 2 >= 1 && Reachable(3, 4, 7, 2) && !Reachable(3, 4, 7, 1), "spec positive 3";
  // (4,5,13) → 2
  expect 2 >= 1 && Reachable(4, 5, 13, 2) && !Reachable(4, 5, 13, 1), "spec positive 4";
  // (25,25,50) → 2
  expect 2 >= 1 && Reachable(25, 25, 50, 2) && !Reachable(25, 25, 50, 1), "spec positive 5";
  // (1,50,50) → 1
  expect 1 >= 1 && Reachable(1, 50, 50, 1) && !Reachable(1, 50, 50, 0), "spec positive 6";
  // (50,1,50) → 1
  expect 1 >= 1 && Reachable(50, 1, 50, 1) && !Reachable(50, 1, 50, 0), "spec positive 7";
  // (3,7,20) → 3
  expect 3 >= 1 && Reachable(3, 7, 20, 3) && !Reachable(3, 7, 20, 2), "spec positive 8";
  // (1,1,2) → 2
  expect 2 >= 1 && Reachable(1, 1, 2, 2) && !Reachable(1, 1, 2, 1), "spec positive 9";
  // (49,49,50) → 1
  expect 1 >= 1 && Reachable(49, 49, 50, 1) && !Reachable(49, 49, 50, 0), "spec positive 10";
  // (7,3,25) → 3
  expect 3 >= 1 && Reachable(7, 3, 25, 3) && !Reachable(7, 3, 25, 2), "spec positive 11";
  // (2,3,15) → 4
  expect 4 >= 1 && Reachable(2, 3, 15, 4) && !Reachable(2, 3, 15, 3), "spec positive 12";
  // (5,5,30) → 4
  expect 4 >= 1 && Reachable(5, 5, 30, 4) && !Reachable(5, 5, 30, 3), "spec positive 13";
  // (1,10,50) → 4
  expect 4 >= 1 && Reachable(1, 10, 50, 4) && !Reachable(1, 10, 50, 3), "spec positive 14";
  // (1,1,10) → 5
  expect 5 >= 1 && Reachable(1, 1, 10, 5) && !Reachable(1, 1, 10, 4), "spec positive 15";
  // (1,1,50) → 8
  expect 8 >= 1 && Reachable(1, 1, 50, 8) && !Reachable(1, 1, 50, 7), "spec positive 16";

  // ============ SPEC NEGATIVE TESTS ============
  // Verify the ensures predicate rejects wrong outputs

  // Neg 1: (1,2,3) wrong=3, correct=2
  expect !(3 >= 1 && Reachable(1, 2, 3, 3) && !Reachable(1, 2, 3, 2)), "spec negative 1";
  // Neg 2: (1,1,1) wrong=2, correct=1
  expect !(2 >= 1 && Reachable(1, 1, 1, 2) && !Reachable(1, 1, 1, 1)), "spec negative 2";
  // Neg 3: (1,1,1) wrong=2, correct=1
  expect !(2 >= 1 && Reachable(1, 1, 1, 2) && !Reachable(1, 1, 1, 1)), "spec negative 3";
  // Neg 4: (1,1,50) wrong=9, correct=8
  expect !(9 >= 1 && Reachable(1, 1, 50, 9) && !Reachable(1, 1, 50, 8)), "spec negative 4";
  // Neg 5: (1,2,3) wrong=3, correct=2
  expect !(3 >= 1 && Reachable(1, 2, 3, 3) && !Reachable(1, 2, 3, 2)), "spec negative 5";
  // Neg 6: (25,25,50) wrong=3, correct=2
  expect !(3 >= 1 && Reachable(25, 25, 50, 3) && !Reachable(25, 25, 50, 2)), "spec negative 6";
  // Neg 7: (1,50,50) wrong=2, correct=1
  expect !(2 >= 1 && Reachable(1, 50, 50, 2) && !Reachable(1, 50, 50, 1)), "spec negative 7";
  // Neg 8: (50,1,50) wrong=2, correct=1
  expect !(2 >= 1 && Reachable(50, 1, 50, 2) && !Reachable(50, 1, 50, 1)), "spec negative 8";
  // Neg 9: (3,7,20) wrong=4, correct=3
  expect !(4 >= 1 && Reachable(3, 7, 20, 4) && !Reachable(3, 7, 20, 3)), "spec negative 9";
  // Neg 10: (1,1,10) wrong=6, correct=5
  expect !(6 >= 1 && Reachable(1, 1, 10, 6) && !Reachable(1, 1, 10, 5)), "spec negative 10";

  // ============ IMPLEMENTATION TESTS ============

  // Test 1
  result := CPlusEqual(1, 2, 3);
  expect result == 2, "impl test 1a failed";
  result := CPlusEqual(5, 4, 100);
  expect result == 7, "impl test 1b failed";

  // Test 2
  result := CPlusEqual(1, 1, 1);
  expect result == 1, "impl test 2a failed";
  result := CPlusEqual(3, 4, 7);
  expect result == 2, "impl test 2b failed";
  result := CPlusEqual(4, 5, 13);
  expect result == 2, "impl test 2c failed";
  result := CPlusEqual(456, 123, 7890123);
  expect result == 21, "impl test 2d failed";
  result := CPlusEqual(1, 1, 1000000000);
  expect result == 43, "impl test 2e failed";
  result := CPlusEqual(45, 12, 782595420);
  expect result == 36, "impl test 2f failed";
  result := CPlusEqual(1, 1000000000, 1000000000);
  expect result == 1, "impl test 2g failed";
  result := CPlusEqual(1, 999999999, 1000000000);
  expect result == 2, "impl test 2h failed";
  result := CPlusEqual(1, 99999, 676497416);
  expect result == 20, "impl test 2i failed";
  result := CPlusEqual(5, 6, 930234861);
  expect result == 40, "impl test 2j failed";
  result := CPlusEqual(8, 9, 881919225);
  expect result == 38, "impl test 2k failed";
  result := CPlusEqual(500000000, 500000000, 1000000000);
  expect result == 2, "impl test 2l failed";
  result := CPlusEqual(1000000000, 1000000000, 1000000000);
  expect result == 1, "impl test 2m failed";
  result := CPlusEqual(999999999, 1000000000, 1000000000);
  expect result == 1, "impl test 2n failed";
  result := CPlusEqual(666, 999999, 987405273);
  expect result == 16, "impl test 2o failed";
  result := CPlusEqual(5378, 5378, 652851553);
  expect result == 24, "impl test 2p failed";

  // Test 4
  result := CPlusEqual(1, 1, 50);
  expect result == 8, "impl test 4 failed";

  // Test 6
  result := CPlusEqual(25, 25, 50);
  expect result == 2, "impl test 6 failed";

  // Test 7
  result := CPlusEqual(1, 50, 50);
  expect result == 1, "impl test 7 failed";

  // Test 8
  result := CPlusEqual(50, 1, 50);
  expect result == 1, "impl test 8 failed";

  // Test 9
  result := CPlusEqual(3, 7, 20);
  expect result == 3, "impl test 9 failed";

  // Test 10
  result := CPlusEqual(1, 1, 10);
  expect result == 5, "impl test 10a failed";
  result := CPlusEqual(2, 3, 15);
  expect result == 4, "impl test 10b failed";
  result := CPlusEqual(5, 5, 30);
  expect result == 4, "impl test 10c failed";
  result := CPlusEqual(1, 10, 50);
  expect result == 4, "impl test 10d failed";
  result := CPlusEqual(7, 3, 25);
  expect result == 3, "impl test 10e failed";

  // Test 11
  result := CPlusEqual(1, 1, 2);
  expect result == 2, "impl test 11 failed";

  // Test 12
  result := CPlusEqual(49, 49, 50);
  expect result == 1, "impl test 12 failed";

  print "All tests passed\n";
}