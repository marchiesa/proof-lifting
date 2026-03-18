function Min(x: int, y: int): int {
  if x <= y then x else y
}

function CandiesAfterDivision(ap: int, bp: int, sp: int, s: int): int
  requires 0 <= s <= sp
{
  Min(ap + s, bp + (sp - s))
}

predicate IsAchievable(a: int, b: int, c: int, result: int)
  requires a >= 0 && b >= 0 && c >= 0
{
  (exists s | 0 <= s <= c :: CandiesAfterDivision(a, b, c, s) == result)
  || (exists s | 0 <= s <= b :: CandiesAfterDivision(a, c, b, s) == result)
  || (exists s | 0 <= s <= a :: CandiesAfterDivision(b, c, a, s) == result)
}

predicate IsOptimal(a: int, b: int, c: int, result: int)
  requires a >= 0 && b >= 0 && c >= 0
{
  (forall s | 0 <= s <= c :: CandiesAfterDivision(a, b, c, s) <= result)
  && (forall s | 0 <= s <= b :: CandiesAfterDivision(a, c, b, s) <= result)
  && (forall s | 0 <= s <= a :: CandiesAfterDivision(b, c, a, s) <= result)
}

method ThreePilesOfCandies(a: int, b: int, c: int) returns (maxCandies: int)
  requires a >= 0 && b >= 0 && c >= 0
  ensures IsAchievable(a, b, c, maxCandies)
  ensures IsOptimal(a, b, c, maxCandies)
{
  maxCandies := (a + b + c) / 2;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Both ensures predicates must hold for correct outputs (small inputs only)

  // From Test 1, case 1: (1, 3, 4) -> 4
  expect IsAchievable(1, 3, 4, 4), "spec positive 1a";
  expect IsOptimal(1, 3, 4, 4), "spec positive 1b";

  // Scaled from Test 1, case 2: (1, 10, 100) -> 55, scaled to (1, 2, 5) -> 4
  expect IsAchievable(1, 2, 5, 4), "spec positive 2a";
  expect IsOptimal(1, 2, 5, 4), "spec positive 2b";

  // Scaled from Test 1, case 3: equal piles (10^16 each), scaled to (2, 2, 2) -> 3
  expect IsAchievable(2, 2, 2, 3), "spec positive 3a";
  expect IsOptimal(2, 2, 2, 3), "spec positive 3b";

  // Scaled from Test 1, case 4: (23, 34, 45) -> 51, scaled to (2, 3, 4) -> 4
  expect IsAchievable(2, 3, 4, 4), "spec positive 4a";
  expect IsOptimal(2, 3, 4, 4), "spec positive 4b";

  // Scaled from Test 2: (111, 2, 3) -> 58, scaled to (5, 2, 3) -> 5
  expect IsAchievable(5, 2, 3, 5), "spec positive 5a";
  expect IsOptimal(5, 2, 3, 5), "spec positive 5b";

  // Additional edge cases
  expect IsAchievable(0, 0, 0, 0), "spec positive 6a";
  expect IsOptimal(0, 0, 0, 0), "spec positive 6b";

  expect IsAchievable(1, 1, 0, 1), "spec positive 7a";
  expect IsOptimal(1, 1, 0, 1), "spec positive 7b";

  // === SPEC NEGATIVE TESTS ===
  // Wrong outputs must be rejected by at least one ensures predicate

  // From Negative 1, case 1: (1, 3, 4) wrong=5 (correct=4)
  expect !IsAchievable(1, 3, 4, 5), "spec negative 1";

  // Scaled from Negative 1 remaining cases: (1, 2, 5) wrong=5 (correct=4)
  expect !IsAchievable(1, 2, 5, 5), "spec negative 2";

  // Scaled: (2, 2, 2) wrong=4 (correct=3)
  expect !IsAchievable(2, 2, 2, 4), "spec negative 3";

  // Scaled: (2, 3, 4) wrong=5 (correct=4)
  expect !IsAchievable(2, 3, 4, 5), "spec negative 4";

  // Scaled from Negative 2: (5, 2, 3) wrong=6 (correct=5)
  expect !IsAchievable(5, 2, 3, 6), "spec negative 5";

  // Additional: (0, 0, 0) wrong=1 (correct=0)
  expect !IsAchievable(0, 0, 0, 1), "spec negative 6";

  // Additional: (1, 1, 0) wrong=2 (correct=1)
  expect !IsAchievable(1, 1, 0, 2), "spec negative 7";

  // === IMPLEMENTATION TESTS ===
  // Full-size test pairs, checking method return values

  // Test 1, case 1
  var r1 := ThreePilesOfCandies(1, 3, 4);
  expect r1 == 4, "impl test 1 failed";

  // Test 1, case 2
  var r2 := ThreePilesOfCandies(1, 10, 100);
  expect r2 == 55, "impl test 2 failed";

  // Test 1, case 3
  var r3 := ThreePilesOfCandies(10000000000000000, 10000000000000000, 10000000000000000);
  expect r3 == 15000000000000000, "impl test 3 failed";

  // Test 1, case 4
  var r4 := ThreePilesOfCandies(23, 34, 45);
  expect r4 == 51, "impl test 4 failed";

  // Test 2, case 1
  var r5 := ThreePilesOfCandies(111, 2, 3);
  expect r5 == 58, "impl test 5 failed";

  print "All tests passed\n";
}