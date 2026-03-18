predicate FitsSideBySide(w1: int, h1: int, w2: int, h2: int, s: int)
{
  w1 + w2 <= s && h1 <= s && h2 <= s
}

predicate FitsStacked(w1: int, h1: int, w2: int, h2: int, s: int)
{
  w1 <= s && w2 <= s && h1 + h2 <= s
}

predicate CanFitInSquare(a: int, b: int, s: int)
{
  FitsSideBySide(a, b, a, b, s) || FitsStacked(a, b, a, b, s) ||
  FitsSideBySide(a, b, b, a, s) || FitsStacked(a, b, b, a, s) ||
  FitsSideBySide(b, a, a, b, s) || FitsStacked(b, a, a, b, s) ||
  FitsSideBySide(b, a, b, a, s) || FitsStacked(b, a, b, a, s)
}

predicate IsMinimalSide(a: int, b: int, s: int)
{
  CanFitInSquare(a, b, s) && forall s' | 1 <= s' < s :: !CanFitInSquare(a, b, s')
}

// Top-level spec predicate derived from the ensures clause
predicate MeetsSpec(a: int, b: int, area: int)
  requires 1 <= a && 1 <= b
{
  exists s | 1 <= s <= 2 * (a + b) :: area == s * s && IsMinimalSide(a, b, s)
}

method MinimalSquare(a: int, b: int) returns (area: int)
  requires 1 <= a && 1 <= b
  ensures exists s | 1 <= s <= 2 * (a + b) :: area == s * s && IsMinimalSide(a, b, s)
{
  var lo := if a < b then a else b;
  var hi := if a < b then b else a;
  var val := if 2 * lo > hi then 2 * lo else hi;
  area := val * val;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // MeetsSpec(a, b, correct_area) should be true
  expect MeetsSpec(3, 2, 16),   "spec positive 1";   // Test 1,2
  expect MeetsSpec(1, 1, 4),    "spec positive 2";   // Test 3
  expect MeetsSpec(5, 5, 100),  "spec positive 3";   // Test 4
  expect MeetsSpec(2, 7, 49),   "spec positive 4";   // Test 5
  expect MeetsSpec(2, 1, 4),    "spec positive 5";   // Test 6,10
  expect MeetsSpec(7, 4, 64),   "spec positive 6";   // Test 7
  expect MeetsSpec(6, 3, 36),   "spec positive 7";   // Test 8
  expect MeetsSpec(10, 5, 100), "spec positive 8";   // Test 9
  expect MeetsSpec(4, 2, 16),   "spec positive 9";   // Test 1
  expect MeetsSpec(3, 3, 36),   "spec positive 10";  // Test 6

  // === SPEC NEGATIVE TESTS ===
  // MeetsSpec(a, b, wrong_area) should be false
  expect !MeetsSpec(3, 2, 17),   "spec negative 1";  // Neg 1,2: wrong 17
  expect !MeetsSpec(1, 1, 5),    "spec negative 2";  // Neg 3,6: wrong 5
  expect !MeetsSpec(5, 5, 101),  "spec negative 3";  // Neg 4: wrong 101
  expect !MeetsSpec(2, 7, 50),   "spec negative 4";  // Neg 5: wrong 50
  expect !MeetsSpec(7, 4, 65),   "spec negative 5";  // Neg 7: wrong 65
  expect !MeetsSpec(6, 3, 37),   "spec negative 6";  // Neg 8: wrong 37
  expect !MeetsSpec(10, 5, 101), "spec negative 7";  // Neg 9: wrong 101
  expect !MeetsSpec(2, 1, 5),    "spec negative 8";  // Neg 10: wrong 5

  // === IMPLEMENTATION TESTS ===
  var r1 := MinimalSquare(3, 2);
  expect r1 == 16, "impl test 1 failed";
  var r2 := MinimalSquare(4, 2);
  expect r2 == 16, "impl test 2 failed";
  var r3 := MinimalSquare(1, 1);
  expect r3 == 4, "impl test 3 failed";
  var r4 := MinimalSquare(3, 1);
  expect r4 == 9, "impl test 4 failed";
  var r5 := MinimalSquare(4, 7);
  expect r5 == 64, "impl test 5 failed";
  var r6 := MinimalSquare(1, 3);
  expect r6 == 9, "impl test 6 failed";
  var r7 := MinimalSquare(7, 4);
  expect r7 == 64, "impl test 7 failed";
  var r8 := MinimalSquare(100, 100);
  expect r8 == 40000, "impl test 8 failed";
  var r9 := MinimalSquare(5, 5);
  expect r9 == 100, "impl test 9 failed";
  var r10 := MinimalSquare(2, 7);
  expect r10 == 49, "impl test 10 failed";
  var r11 := MinimalSquare(4, 4);
  expect r11 == 64, "impl test 11 failed";
  var r12 := MinimalSquare(2, 1);
  expect r12 == 4, "impl test 12 failed";
  var r13 := MinimalSquare(1, 2);
  expect r13 == 4, "impl test 13 failed";
  var r14 := MinimalSquare(3, 3);
  expect r14 == 36, "impl test 14 failed";
  var r15 := MinimalSquare(5, 3);
  expect r15 == 36, "impl test 15 failed";
  var r16 := MinimalSquare(6, 3);
  expect r16 == 36, "impl test 16 failed";
  var r17 := MinimalSquare(3, 6);
  expect r17 == 36, "impl test 17 failed";
  var r18 := MinimalSquare(10, 5);
  expect r18 == 100, "impl test 18 failed";
  var r19 := MinimalSquare(1, 50);
  expect r19 == 2500, "impl test 19 failed";
  var r20 := MinimalSquare(25, 25);
  expect r20 == 2500, "impl test 20 failed";
  var r21 := MinimalSquare(8, 3);
  expect r21 == 64, "impl test 21 failed";
  var r22 := MinimalSquare(50, 50);
  expect r22 == 10000, "impl test 22 failed";
  var r23 := MinimalSquare(1, 49);
  expect r23 == 2401, "impl test 23 failed";
  var r24 := MinimalSquare(30, 15);
  expect r24 == 900, "impl test 24 failed";

  print "All tests passed\n";
}