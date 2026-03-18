function ReachableIn(start: int, steps: int): set<int>
  requires start >= 0
  requires steps >= 0
  decreases steps
{
  if steps == 0 then
    {start}
  else
    var prev := ReachableIn(start, steps - 1);
    prev + set v <- prev, d <- {-5, -2, -1, 1, 2, 5} | v + d >= 0 :: v + d
}

method ChangingVolume(a: int, b: int) returns (presses: int)
  requires a >= 0 && b >= 0
  ensures presses >= 0
  ensures b in ReachableIn(a, presses)
  ensures presses > 0 ==> b !in ReachableIn(a, presses - 1)
{
  var diff := if a > b then a - b else b - a;
  var fives := diff / 5;
  diff := diff % 5;
  var twos := diff / 2;
  diff := diff % 2;
  var ones := diff;
  presses := fives + twos + ones;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Ensures: b in ReachableIn(a, p) && (p == 0 || b !in ReachableIn(a, p-1))

  // From Test 2: (0, 0) -> 0
  expect 0 in ReachableIn(0, 0), "spec positive 1";

  // From Test 3: (10, 10) -> 0
  expect 10 in ReachableIn(10, 0), "spec positive 2";

  // From Test 4: (0, 5) -> 1
  expect 5 in ReachableIn(0, 1) && 5 !in ReachableIn(0, 0), "spec positive 3";

  // From Test 5: (3, 0) -> 2
  expect 0 in ReachableIn(3, 2) && 0 !in ReachableIn(3, 1), "spec positive 4";

  // From Test 9: (0, 1) -> 1
  expect 1 in ReachableIn(0, 1) && 1 !in ReachableIn(0, 0), "spec positive 5";

  // From Test 9: (1, 0) -> 1
  expect 0 in ReachableIn(1, 1) && 0 !in ReachableIn(1, 0), "spec positive 6";

  // From Test 9: (2, 5) -> 2
  expect 5 in ReachableIn(2, 2) && 5 !in ReachableIn(2, 1), "spec positive 7";

  // From Test 9: (10, 3) -> 2
  expect 3 in ReachableIn(10, 2) && 3 !in ReachableIn(10, 1), "spec positive 8";

  // From Test 9: (7, 7) -> 0
  expect 7 in ReachableIn(7, 0), "spec positive 9";

  // From Test 10: (5, 5) -> 0
  expect 5 in ReachableIn(5, 0), "spec positive 10";

  // From Test 10: (1, 2) -> 1
  expect 2 in ReachableIn(1, 1) && 2 !in ReachableIn(1, 0), "spec positive 11";

  // From Test 10: (0, 3) -> 2
  expect 3 in ReachableIn(0, 2) && 3 !in ReachableIn(0, 1), "spec positive 12";

  // From Test 10: (25, 30) -> 1
  expect 30 in ReachableIn(25, 1) && 30 !in ReachableIn(25, 0), "spec positive 13";

  // From Test 10: (12, 7) -> 1
  expect 7 in ReachableIn(12, 1) && 7 !in ReachableIn(12, 0), "spec positive 14";

  // From Test 1: (4, 0) -> 2
  expect 0 in ReachableIn(4, 2) && 0 !in ReachableIn(4, 1), "spec positive 15";

  // From Test 1: (3, 9) -> 2
  expect 9 in ReachableIn(3, 2) && 9 !in ReachableIn(3, 1), "spec positive 16";

  // From Test 10: (48, 41) -> 2
  expect 41 in ReachableIn(48, 2) && 41 !in ReachableIn(48, 1), "spec positive 17";

  // From Test 8: (7, 18) -> 3
  expect 18 in ReachableIn(7, 3) && 18 !in ReachableIn(7, 2), "spec positive 18";

  // From Test 1: (5, 14) -> 3
  expect 14 in ReachableIn(5, 3) && 14 !in ReachableIn(5, 2), "spec positive 19";

  // ===== SPEC NEGATIVE TESTS =====
  // Wrong answer must NOT satisfy the full ensures conjunction

  // From Neg 1: (4, 0) -> wrong=3 (correct=2)
  expect !(0 in ReachableIn(4, 3) && 0 !in ReachableIn(4, 2)), "spec negative 1";

  // From Neg 2: (0, 0) -> wrong=1 (correct=0)
  expect !(0 in ReachableIn(0, 1) && 0 !in ReachableIn(0, 0)), "spec negative 2";

  // From Neg 3: (10, 10) -> wrong=1 (correct=0)
  expect !(10 in ReachableIn(10, 1) && 10 !in ReachableIn(10, 0)), "spec negative 3";

  // From Neg 4: (0, 5) -> wrong=2 (correct=1)
  expect !(5 in ReachableIn(0, 2) && 5 !in ReachableIn(0, 1)), "spec negative 4";

  // From Neg 5: (3, 0) -> wrong=3 (correct=2)
  expect !(0 in ReachableIn(3, 3) && 0 !in ReachableIn(3, 2)), "spec negative 5";

  // From Neg 9: (0, 1) -> wrong=2 (correct=1)
  expect !(1 in ReachableIn(0, 2) && 1 !in ReachableIn(0, 1)), "spec negative 6";

  // ===== IMPLEMENTATION TESTS =====

  // Test 1
  var r1 := ChangingVolume(4, 0);
  expect r1 == 2, "impl test 1.1 failed";
  var r2 := ChangingVolume(5, 14);
  expect r2 == 3, "impl test 1.2 failed";
  var r3 := ChangingVolume(3, 9);
  expect r3 == 2, "impl test 1.3 failed";

  // Test 2
  var r4 := ChangingVolume(0, 0);
  expect r4 == 0, "impl test 2 failed";

  // Test 3
  var r5 := ChangingVolume(10, 10);
  expect r5 == 0, "impl test 3 failed";

  // Test 4
  var r6 := ChangingVolume(0, 5);
  expect r6 == 1, "impl test 4 failed";

  // Test 5
  var r7 := ChangingVolume(3, 0);
  expect r7 == 2, "impl test 5 failed";

  // Test 6
  var r8 := ChangingVolume(1, 50);
  expect r8 == 11, "impl test 6 failed";

  // Test 7
  var r9 := ChangingVolume(50, 1);
  expect r9 == 11, "impl test 7 failed";

  // Test 8
  var r10 := ChangingVolume(7, 18);
  expect r10 == 3, "impl test 8 failed";

  // Test 9
  var r11 := ChangingVolume(0, 1);
  expect r11 == 1, "impl test 9.1 failed";
  var r12 := ChangingVolume(1, 0);
  expect r12 == 1, "impl test 9.2 failed";
  var r13 := ChangingVolume(2, 5);
  expect r13 == 2, "impl test 9.3 failed";
  var r14 := ChangingVolume(10, 3);
  expect r14 == 2, "impl test 9.4 failed";
  var r15 := ChangingVolume(7, 7);
  expect r15 == 0, "impl test 9.5 failed";

  // Test 10
  var r16 := ChangingVolume(0, 50);
  expect r16 == 10, "impl test 10.1 failed";
  var r17 := ChangingVolume(50, 0);
  expect r17 == 10, "impl test 10.2 failed";
  var r18 := ChangingVolume(25, 30);
  expect r18 == 1, "impl test 10.3 failed";
  var r19 := ChangingVolume(12, 7);
  expect r19 == 1, "impl test 10.4 failed";
  var r20 := ChangingVolume(0, 3);
  expect r20 == 2, "impl test 10.5 failed";
  var r21 := ChangingVolume(48, 41);
  expect r21 == 2, "impl test 10.6 failed";
  var r22 := ChangingVolume(5, 5);
  expect r22 == 0, "impl test 10.7 failed";
  var r23 := ChangingVolume(1, 2);
  expect r23 == 1, "impl test 10.8 failed";
  var r24 := ChangingVolume(33, 50);
  expect r24 == 4, "impl test 10.9 failed";
  var r25 := ChangingVolume(17, 9);
  expect r25 == 3, "impl test 10.10 failed";

  print "All tests passed\n";
}