// tests.dfy — Tests for DiceRolling implementation and IsCorrectAnswer spec

// ===== SPEC FUNCTIONS AND PREDICATES =====

function SumSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

predicate ValidDiceFace(v: int)
{
  2 <= v <= 7
}

predicate AllValidFaces(dice: seq<int>)
{
  forall i | 0 <= i < |dice| :: ValidDiceFace(dice[i])
}

function BuildDiceWitness(extra: int, numLeft: int): seq<int>
  requires numLeft >= 0
  decreases numLeft
{
  if numLeft == 0 then []
  else if numLeft == 1 then [2 + extra]
  else
    var add := if extra > 5 then 5 else if extra < 0 then 0 else extra;
    [2 + add] + BuildDiceWitness(extra - add, numLeft - 1)
}

function DiceWitness(target: int, numRolls: int): seq<int>
  requires numRolls >= 1
{
  BuildDiceWitness(target - 2 * numRolls, numRolls)
}

predicate IsCorrectAnswer(target: int, numRolls: int)
{
  if numRolls < 1 then false
  else
    var dice := DiceWitness(target, numRolls);
    |dice| == numRolls &&
    AllValidFaces(dice) &&
    SumSeq(dice) == target
}

// ===== IMPLEMENTATION =====

method DiceRolling(x: seq<int>) returns (rolls: seq<int>)
  requires forall i | 0 <= i < |x| :: x[i] >= 2
  ensures |rolls| == |x|
  ensures forall i | 0 <= i < |rolls| :: IsCorrectAnswer(x[i], rolls[i])
{
  rolls := [];
  var i := 0;
  while i < |x|
  {
    var val := x[i];
    if val <= 7 {
      rolls := rolls + [1];
    } else {
      var r := val / 7;
      if val % 7 != 0 {
        r := r + 1;
      }
      rolls := rolls + [r];
    }
    i := i + 1;
  }
}

// ===== TESTS =====

method Main()
{
  // ========== SPEC POSITIVE TESTS ==========
  // IsCorrectAnswer(target, numRolls) should be true for correct pairs.
  // Using small values extracted from test pairs.

  // From Test 1: target=2, rolls=1
  expect IsCorrectAnswer(2, 1), "spec positive 1";
  // From Test 1: target=13, rolls=2
  expect IsCorrectAnswer(13, 2), "spec positive 2";
  // From Test 6: target=7, rolls=1
  expect IsCorrectAnswer(7, 1), "spec positive 3";
  // From Test 2: target=3, rolls=1
  expect IsCorrectAnswer(3, 1), "spec positive 4";
  // From Test 3: target=5, rolls=1
  expect IsCorrectAnswer(5, 1), "spec positive 5";
  // From Test 3: target=9, rolls=2
  expect IsCorrectAnswer(9, 2), "spec positive 6";
  // From Test 5: target=42, rolls=6 (6 dice, sum 42: feasible, 6*7=42)
  expect IsCorrectAnswer(42, 6), "spec positive 7";

  // ========== SPEC NEGATIVE TESTS ==========
  // IsCorrectAnswer(target, wrongNumRolls) should be false.
  // The wrong values must be infeasible: numRolls*2 > target (too many dice)
  // or numRolls*7 < target (too few dice) or numRolls < 1.
  // Derived from negative test pairs, scaled to small values where needed.

  // From Negative 1: target=2, wrong rolls=2 (min sum with 2 dice is 4 > 2)
  expect !IsCorrectAnswer(2, 2), "spec negative 1";
  // From Negative 2: scaled — target=3, wrong rolls=2 (min sum 4 > 3)
  expect !IsCorrectAnswer(3, 2), "spec negative 2";
  // From Negative 3: scaled — target=4, wrong rolls=3 (min sum 6 > 4)
  expect !IsCorrectAnswer(4, 3), "spec negative 3";
  // From Negative 4: scaled — target=2, wrong rolls=3 (min sum 6 > 2)
  expect !IsCorrectAnswer(2, 3), "spec negative 4";
  // From Negative 5: scaled — target=5, wrong rolls=3 (min sum 6 > 5)
  expect !IsCorrectAnswer(5, 3), "spec negative 5";
  // From Negative 6: scaled — target=3, wrong rolls=3 (min sum 6 > 3)
  expect !IsCorrectAnswer(3, 3), "spec negative 6";

  // ========== IMPLEMENTATION TESTS ==========

  // Test 1
  var r1 := DiceRolling([2, 13, 37, 100]);
  expect r1 == [1, 2, 6, 15], "impl test 1 failed";

  // Test 2
  var r2 := DiceRolling([
    17, 38, 56, 16, 7, 36, 29, 95, 50, 28,
    64, 98, 46, 42, 3, 93, 10, 74, 80, 9,
    55, 31, 51, 34, 35, 82, 96, 69, 54, 77,
    76, 92, 58, 70, 20, 73, 72, 86, 41, 12,
    4, 24, 89, 67, 13, 49, 78, 65, 66, 37,
    61, 84, 39, 99, 79, 48, 25, 23, 62, 14,
    85, 97, 15, 53, 68, 47, 40, 90, 81, 57,
    21, 19, 71, 6, 91, 5, 8, 18, 59, 33,
    87, 22, 2, 11, 27, 94, 26, 32, 83, 100,
    88, 52, 44, 60, 63, 45, 30, 43, 75
  ]);
  expect r2 == [
    3, 6, 8, 3, 1, 6, 5, 14, 8, 4,
    10, 14, 7, 6, 1, 14, 2, 11, 12, 2,
    8, 5, 8, 5, 5, 12, 14, 10, 8, 11,
    11, 14, 9, 10, 3, 11, 11, 13, 6, 2,
    1, 4, 13, 10, 2, 7, 12, 10, 10, 6,
    9, 12, 6, 15, 12, 7, 4, 4, 9, 2,
    13, 14, 3, 8, 10, 7, 6, 13, 12, 9,
    3, 3, 11, 1, 13, 1, 2, 3, 9, 5,
    13, 4, 1, 2, 4, 14, 4, 5, 12, 15,
    13, 8, 7, 9, 9, 7, 5, 7, 11
  ], "impl test 2 failed";

  // Test 3
  var r3 := DiceRolling([
    72, 9, 65, 37, 14, 70, 76, 53, 23, 22,
    5, 20, 13, 24, 35, 46, 29, 50, 88, 76,
    72, 48, 85, 74, 47, 78, 55, 69, 15, 58,
    47, 86, 30, 37, 72, 17, 99, 21, 58, 94,
    44, 62, 52, 41, 93, 74, 19, 53, 14, 31,
    54, 21, 12, 74, 62, 92, 13, 8, 79, 15,
    29, 24, 6, 93, 91, 55, 21, 5, 62, 73,
    28, 15, 86, 27, 92, 20, 61, 95, 36, 61,
    9, 94, 4, 94, 3, 78, 14, 13, 50, 33,
    43, 35, 96, 64, 10, 2, 9, 92, 31, 71
  ]);
  expect r3 == [
    11, 2, 10, 6, 2, 10, 11, 8, 4, 4,
    1, 3, 2, 4, 5, 7, 5, 8, 13, 11,
    11, 7, 13, 11, 7, 12, 8, 10, 3, 9,
    7, 13, 5, 6, 11, 3, 15, 3, 9, 14,
    7, 9, 8, 6, 14, 11, 3, 8, 2, 5,
    8, 3, 2, 11, 9, 14, 2, 2, 12, 3,
    5, 4, 1, 14, 13, 8, 3, 1, 9, 11,
    4, 3, 13, 4, 14, 3, 9, 14, 6, 9,
    2, 14, 1, 14, 1, 12, 2, 2, 8, 5,
    7, 5, 14, 10, 2, 1, 2, 14, 5, 11
  ], "impl test 3 failed";

  // Test 4
  var r4 := DiceRolling([
    100, 100, 100, 100, 100, 100, 100, 100, 100, 100,
    100, 100, 100, 100, 100, 100, 100, 100, 100, 100,
    100, 100, 100, 100, 100, 100, 100, 100, 100, 100,
    100, 100, 100, 100, 100, 100, 100, 100, 100, 100,
    100, 100, 100, 100, 100, 100, 100, 100, 100, 100,
    100, 100, 100, 100, 100, 100, 100, 100, 100, 100,
    100, 100, 100, 100, 100, 100, 100, 100, 100, 100,
    100, 100, 100, 100, 100, 100, 100, 100, 100, 100,
    100, 100, 100, 100, 100, 100, 100, 100, 100, 100,
    100, 100, 100, 100, 100, 100, 100, 100, 100, 100
  ]);
  expect r4 == [
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15
  ], "impl test 4 failed";

  // Test 5
  var r5 := DiceRolling([42]);
  expect r5 == [6], "impl test 5 failed";

  // Test 6
  var r6 := DiceRolling([99, 7]);
  expect r6 == [15, 1], "impl test 6 failed";

  print "All tests passed\n";
}