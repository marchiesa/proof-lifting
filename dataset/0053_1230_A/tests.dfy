function FriendSum(a1: int, a2: int, a3: int, a4: int,
                   b1: bool, b2: bool, b3: bool, b4: bool): int
{
  (if b1 then a1 else 0) + (if b2 then a2 else 0) +
  (if b3 then a3 else 0) + (if b4 then a4 else 0)
}

predicate CanDistributeEqually(a1: int, a2: int, a3: int, a4: int)
{
  exists b1: bool, b2: bool, b3: bool, b4: bool ::
    FriendSum(a1, a2, a3, a4, b1, b2, b3, b4) ==
    FriendSum(a1, a2, a3, a4, !b1, !b2, !b3, !b4)
}

method DawidAndCandies(a1: int, a2: int, a3: int, a4: int) returns (result: bool)
  requires a1 >= 1 && a2 >= 1 && a3 >= 1 && a4 >= 1
  ensures result == CanDistributeEqually(a1, a2, a3, a4)
{
  result := (a1 + a2 == a3 + a4) || (a1 + a3 == a2 + a4) || (a1 + a4 == a2 + a3) ||
            (a1 + a2 + a3 == a4) || (a1 + a2 + a4 == a3) || (a1 + a3 + a4 == a2) || (a2 + a3 + a4 == a1);
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // ensures: result == CanDistributeEqually(a1, a2, a3, a4)
  // The existential quantifier is over 4 bools (16 combos), so all inputs are fine.
  expect CanDistributeEqually(1, 7, 11, 5) == true, "spec positive 1";
  expect CanDistributeEqually(7, 3, 2, 5) == false, "spec positive 2";
  expect CanDistributeEqually(3, 14, 36, 53) == true, "spec positive 3";
  expect CanDistributeEqually(30, 74, 41, 63) == true, "spec positive 4";
  expect CanDistributeEqually(92, 69, 83, 97) == false, "spec positive 5";
  expect CanDistributeEqually(26, 52, 7, 19) == true, "spec positive 6";
  expect CanDistributeEqually(72, 52, 62, 62) == true, "spec positive 7";
  expect CanDistributeEqually(1, 1, 1, 1) == true, "spec positive 8";
  expect CanDistributeEqually(70, 100, 10, 86) == false, "spec positive 9";
  expect CanDistributeEqually(14, 10, 18, 24) == false, "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // Each negative test checks the spec rejects the WRONG output.
  // Wrong output is the negation of the correct one, so spec must disagree with it.
  expect CanDistributeEqually(1, 7, 11, 5) != false, "spec negative 1";
  expect CanDistributeEqually(7, 3, 2, 5) != true, "spec negative 2";
  expect CanDistributeEqually(3, 14, 36, 53) != false, "spec negative 3";
  expect CanDistributeEqually(30, 74, 41, 63) != false, "spec negative 4";
  expect CanDistributeEqually(92, 69, 83, 97) != true, "spec negative 5";
  expect CanDistributeEqually(26, 52, 7, 19) != false, "spec negative 6";
  expect CanDistributeEqually(72, 52, 62, 62) != false, "spec negative 7";
  expect CanDistributeEqually(1, 1, 1, 1) != false, "spec negative 8";
  expect CanDistributeEqually(70, 100, 10, 86) != true, "spec negative 9";
  expect CanDistributeEqually(14, 10, 18, 24) != true, "spec negative 10";

  // === IMPLEMENTATION TESTS ===
  var r1 := DawidAndCandies(1, 7, 11, 5);
  expect r1 == true, "impl test 1 failed";

  var r2 := DawidAndCandies(7, 3, 2, 5);
  expect r2 == false, "impl test 2 failed";

  var r3 := DawidAndCandies(3, 14, 36, 53);
  expect r3 == true, "impl test 3 failed";

  var r4 := DawidAndCandies(30, 74, 41, 63);
  expect r4 == true, "impl test 4 failed";

  var r5 := DawidAndCandies(92, 69, 83, 97);
  expect r5 == false, "impl test 5 failed";

  var r6 := DawidAndCandies(26, 52, 7, 19);
  expect r6 == true, "impl test 6 failed";

  var r7 := DawidAndCandies(72, 52, 62, 62);
  expect r7 == true, "impl test 7 failed";

  var r8 := DawidAndCandies(1, 1, 1, 1);
  expect r8 == true, "impl test 8 failed";

  var r9 := DawidAndCandies(70, 100, 10, 86);
  expect r9 == false, "impl test 9 failed";

  var r10 := DawidAndCandies(14, 10, 18, 24);
  expect r10 == false, "impl test 10 failed";

  var r11 := DawidAndCandies(20, 14, 37, 71);
  expect r11 == true, "impl test 11 failed";

  var r12 := DawidAndCandies(1, 1, 2, 1);
  expect r12 == false, "impl test 12 failed";

  var r13 := DawidAndCandies(2, 4, 1, 1);
  expect r13 == true, "impl test 13 failed";

  var r14 := DawidAndCandies(34, 11, 84, 39);
  expect r14 == true, "impl test 14 failed";

  var r15 := DawidAndCandies(76, 97, 99, 74);
  expect r15 == true, "impl test 15 failed";

  var r16 := DawidAndCandies(44, 58, 90, 53);
  expect r16 == false, "impl test 16 failed";

  var r17 := DawidAndCandies(18, 88, 18, 18);
  expect r17 == false, "impl test 17 failed";

  var r18 := DawidAndCandies(48, 14, 3, 31);
  expect r18 == true, "impl test 18 failed";

  var r19 := DawidAndCandies(72, 96, 2, 26);
  expect r19 == true, "impl test 19 failed";

  var r20 := DawidAndCandies(69, 7, 44, 30);
  expect r20 == false, "impl test 20 failed";

  print "All tests passed\n";
}