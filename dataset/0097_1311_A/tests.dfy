predicate ValidStep(from: int, to: int) {
  (to > from && (to - from) % 2 == 1)
  ||
  (from - to >= 2 && (from - to) % 2 == 0)
}

predicate ReachableIn(a: int, b: int, steps: nat)
  decreases steps
{
  if steps == 0 then
    a == b
  else if steps == 1 then
    ValidStep(a, b)
  else
    exists c | a - 2 <= c <= a + 2 ::
      ValidStep(a, c) && ReachableIn(c, b, steps - 1)
}

// Combined ensures predicate: correct moves count with minimality
predicate SpecOk(a: int, b: int, moves: nat) {
  moves <= 2
  && ReachableIn(a, b, moves)
  && (moves < 1 || !ReachableIn(a, b, 0))
  && (moves < 2 || !ReachableIn(a, b, 1))
}

method AddOddOrSubtractEven(a: int, b: int) returns (moves: int)
  requires a >= 1 && b >= 1
  ensures 0 <= moves <= 2
  ensures ReachableIn(a, b, moves)
  ensures forall k | 0 <= k < moves :: !ReachableIn(a, b, k)
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
  // ===== SPEC POSITIVE TESTS =====
  // SpecOk accepts correct (a, b, moves) triples — small inputs only

  // SP1: (2,3)->1 [diff parity, b>a]
  expect SpecOk(2, 3, 1), "spec positive 1";
  // SP2: (1,1)->0 [equal, scaled from (10,10), (55678978,55678978)]
  expect SpecOk(1, 1, 0), "spec positive 2";
  // SP3: (2,4)->2 [same parity, b>a]
  expect SpecOk(2, 4, 2), "spec positive 3";
  // SP4: (3,1)->1 [same parity, a>b, scaled from (9,3)]
  expect SpecOk(3, 1, 1), "spec positive 4";
  // SP5: (1,2)->1 [diff parity, b>a]
  expect SpecOk(1, 2, 1), "spec positive 5";
  // SP6: (5,5)->0 [equal]
  expect SpecOk(5, 5, 0), "spec positive 6";
  // SP7: (1,3)->2 [same parity, b>a, scaled from (3,7)]
  expect SpecOk(1, 3, 2), "spec positive 7";
  // SP8: (4,2)->1 [same parity, a>b, scaled from (10,4)]
  expect SpecOk(4, 2, 1), "spec positive 8";
  // SP9: (1,4)->1 [diff parity, b>a, scaled from (1,50)]
  expect SpecOk(1, 4, 1), "spec positive 9";
  // SP10: (3,2)->2 [diff parity, a>b, scaled from (7,4)]
  expect SpecOk(3, 2, 2), "spec positive 10";

  // ===== SPEC NEGATIVE TESTS =====
  // SpecOk rejects wrong (a, b, moves) triples — small inputs only

  // SN1: (2,3) wrong=2, correct=1 [from neg 1]
  expect !SpecOk(2, 3, 2), "spec negative 1";
  // SN2: (3,2) wrong=3 [from neg 2: (19260817,114514) wrong=3, scaled down]
  expect !SpecOk(3, 2, 3), "spec negative 2";
  // SN3: (5,2) wrong=3 [from neg 3: (484887,54) wrong=3, scaled down]
  expect !SpecOk(5, 2, 3), "spec negative 3";
  // SN4: (2,2) wrong=1 [from neg 4: (55678978,55678978) wrong=1, scaled down]
  expect !SpecOk(2, 2, 1), "spec negative 4";
  // SN5: (1,2) wrong=2, correct=1 [from neg 5]
  expect !SpecOk(1, 2, 2), "spec negative 5";
  // SN6: (5,5) wrong=1, correct=0 [from neg 6]
  expect !SpecOk(5, 5, 1), "spec negative 6";
  // SN7: (1,3) wrong=3 [from neg 7: (3,7) wrong=3, scaled down]
  expect !SpecOk(1, 3, 3), "spec negative 7";
  // SN8: (4,2) wrong=2, correct=1 [from neg 8: (10,4) wrong=2, scaled down]
  expect !SpecOk(4, 2, 2), "spec negative 8";
  // SN9: (1,4) wrong=2, correct=1 [from neg 9: (1,50) wrong=2, scaled down]
  expect !SpecOk(1, 4, 2), "spec negative 9";
  // SN10: (2,3) wrong=2 [from neg 10]
  expect !SpecOk(2, 3, 2), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  var result: int;

  // Test 1 (5 pairs)
  result := AddOddOrSubtractEven(2, 3);
  expect result == 1, "impl test 1a failed";
  result := AddOddOrSubtractEven(10, 10);
  expect result == 0, "impl test 1b failed";
  result := AddOddOrSubtractEven(2, 4);
  expect result == 2, "impl test 1c failed";
  result := AddOddOrSubtractEven(7, 4);
  expect result == 2, "impl test 1d failed";
  result := AddOddOrSubtractEven(9, 3);
  expect result == 1, "impl test 1e failed";

  // Test 2
  result := AddOddOrSubtractEven(19260817, 114514);
  expect result == 2, "impl test 2 failed";

  // Test 3
  result := AddOddOrSubtractEven(484887, 54);
  expect result == 2, "impl test 3 failed";

  // Test 4
  result := AddOddOrSubtractEven(55678978, 55678978);
  expect result == 0, "impl test 4 failed";

  // Test 5
  result := AddOddOrSubtractEven(1, 2);
  expect result == 1, "impl test 5 failed";

  // Test 6
  result := AddOddOrSubtractEven(5, 5);
  expect result == 0, "impl test 6 failed";

  // Test 7
  result := AddOddOrSubtractEven(3, 7);
  expect result == 2, "impl test 7 failed";

  // Test 8
  result := AddOddOrSubtractEven(10, 4);
  expect result == 1, "impl test 8 failed";

  // Test 9
  result := AddOddOrSubtractEven(1, 50);
  expect result == 1, "impl test 9 failed";

  // Test 10
  result := AddOddOrSubtractEven(2, 3);
  expect result == 1, "impl test 10a failed";
  result := AddOddOrSubtractEven(10, 10);
  expect result == 0, "impl test 10b failed";
  result := AddOddOrSubtractEven(7, 4);
  expect result == 2, "impl test 10c failed";

  // Test 11
  result := AddOddOrSubtractEven(49, 50);
  expect result == 1, "impl test 11a failed";
  result := AddOddOrSubtractEven(1, 1);
  expect result == 0, "impl test 11b failed";

  // Test 12
  result := AddOddOrSubtractEven(1, 1);
  expect result == 0, "impl test 12a failed";
  result := AddOddOrSubtractEven(2, 2);
  expect result == 0, "impl test 12b failed";
  result := AddOddOrSubtractEven(3, 3);
  expect result == 0, "impl test 12c failed";
  result := AddOddOrSubtractEven(4, 4);
  expect result == 0, "impl test 12d failed";

  // Test 13
  result := AddOddOrSubtractEven(25, 13);
  expect result == 1, "impl test 13 failed";

  // Test 14
  result := AddOddOrSubtractEven(1, 3);
  expect result == 2, "impl test 14a failed";
  result := AddOddOrSubtractEven(4, 2);
  expect result == 1, "impl test 14b failed";
  result := AddOddOrSubtractEven(7, 8);
  expect result == 1, "impl test 14c failed";
  result := AddOddOrSubtractEven(50, 1);
  expect result == 2, "impl test 14d failed";
  result := AddOddOrSubtractEven(33, 47);
  expect result == 2, "impl test 14e failed";

  print "All tests passed\n";
}