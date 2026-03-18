function Pow(base: nat, exp: nat): nat
  decreases exp
{
  if exp == 0 then 1 else base * Pow(base, exp - 1)
}

function FightWinner(levels: seq<int>, i: int, j: int): int
  requires 0 <= i < |levels| && 0 <= j < |levels| && i != j
{
  if levels[i] > levels[j] then i
  else if levels[j] > levels[i] then j
  else -1
}

function AfterFight(levels: seq<int>, i: int, j: int): (result: seq<int>)
  requires 0 <= i < |levels| && 0 <= j < |levels| && i != j
  ensures |result| == |levels|
{
  var w := FightWinner(levels, i, j);
  if w >= 0 then levels[w := levels[w] + 1] else levels
}

predicate CanAccumulateWins(levels: seq<int>, h: int, winsNeeded: nat, fuel: nat)
  requires |levels| >= 2
  requires 0 <= h < |levels|
  decreases fuel
{
  winsNeeded == 0
  ||
  (fuel > 0 &&
   exists i, j | 0 <= i < |levels| && 0 <= j < |levels| && i != j ::
     var w := FightWinner(levels, i, j);
     var newLevels := AfterFight(levels, i, j);
     var gained: nat := if w == h then 1 else 0;
     CanAccumulateWins(newLevels, h, winsNeeded - gained, fuel - 1))
}

predicate IsPossibleWinner(levels: seq<int>, h: int)
  requires |levels| >= 2
  requires 0 <= h < |levels|
{
  CanAccumulateWins(levels, h, Pow(100, 500), Pow(100, 500))
}

function CountPossibleWinners(levels: seq<int>): int
  requires |levels| >= 2
{
  CountPossibleWinnersHelper(levels, |levels|)
}

function CountPossibleWinnersHelper(levels: seq<int>, k: int): int
  requires |levels| >= 2
  requires 0 <= k <= |levels|
  decreases k
{
  if k == 0 then 0
  else
    (if IsPossibleWinner(levels, k - 1) then 1 else 0) +
    CountPossibleWinnersHelper(levels, k - 1)
}

// Runtime-feasible equivalent of CountPossibleWinners.
// Uses CanAccumulateWins with winsNeeded=1, fuel=1 instead of Pow(100,500).
// Semantically equivalent: a hero that can win 1 fight can win arbitrarily
// many, because each victory increases their level by 1.
function CountPossibleWinnersTestable(levels: seq<int>): int
  requires |levels| >= 2
{
  CountPossibleWinnersHelperTestable(levels, |levels|)
}

function CountPossibleWinnersHelperTestable(levels: seq<int>, k: int): int
  requires |levels| >= 2
  requires 0 <= k <= |levels|
  decreases k
{
  if k == 0 then 0
  else
    (if CanAccumulateWins(levels, k - 1, 1, 1) then 1 else 0) +
    CountPossibleWinnersHelperTestable(levels, k - 1)
}

method Arena(n: int, a: seq<int>) returns (count: int)
  requires |a| >= 2
  ensures count == CountPossibleWinners(a)
{
  var min_hero := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < min_hero {
      min_hero := a[i];
    }
    i := i + 1;
  }
  count := 0;
  i := 0;
  while i < |a|
  {
    if a[i] > min_hero {
      count := count + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  // ========== SPEC POSITIVE TESTS ==========
  // Using CountPossibleWinnersTestable (runtime-feasible equivalent of CountPossibleWinners).
  // Inputs scaled to length 2-3, values 0-5 for feasible bounded quantifier enumeration.
  expect CountPossibleWinnersTestable([3, 2, 2]) == 1, "spec positive 1";   // test 1a
  expect CountPossibleWinnersTestable([5, 5]) == 0, "spec positive 2";      // test 1b
  expect CountPossibleWinnersTestable([1, 3, 3]) == 2, "spec positive 3";   // test 1c scaled [1,3,3,7]->3
  expect CountPossibleWinnersTestable([1, 1, 1]) == 0, "spec positive 4";   // test 2 scaled
  expect CountPossibleWinnersTestable([5, 5, 5]) == 0, "spec positive 5";   // test 3 scaled
  expect CountPossibleWinnersTestable([2, 2, 2]) == 0, "spec positive 6";   // test 4a
  expect CountPossibleWinnersTestable([2, 2]) == 0, "spec positive 7";      // test 4b
  expect CountPossibleWinnersTestable([1, 1, 2]) == 1, "spec positive 8";   // test 5 scaled
  expect CountPossibleWinnersTestable([1, 2, 3]) == 2, "spec positive 9";   // test 6 scaled [90,91,92]->2
  expect CountPossibleWinnersTestable([1, 1]) == 0, "spec positive 10";     // test 7b
  expect CountPossibleWinnersTestable([3, 3, 3]) == 0, "spec positive 11";  // test 9a
  expect CountPossibleWinnersTestable([3, 3]) == 0, "spec positive 12";     // test 9b

  // ========== SPEC NEGATIVE TESTS ==========
  // Verifies that the spec rejects wrong outputs from negative test pairs.
  expect CountPossibleWinnersTestable([3, 2, 2]) != 2, "spec negative 1";   // neg 1: wrong 2, correct 1
  expect CountPossibleWinnersTestable([1, 1, 1]) != 1, "spec negative 2";   // neg 2 scaled: wrong 1, correct 0
  expect CountPossibleWinnersTestable([5, 5]) != 1, "spec negative 3";      // neg 3 scaled: wrong 1, correct 0
  expect CountPossibleWinnersTestable([2, 2, 2]) != 1, "spec negative 4";   // neg 4: wrong 1, correct 0
  expect CountPossibleWinnersTestable([1, 1, 2]) != 2, "spec negative 5";   // neg 5 scaled: wrong 2, correct 1
  expect CountPossibleWinnersTestable([1, 2, 3]) != 3, "spec negative 6";   // neg 6 scaled: wrong 3, correct 2
  expect CountPossibleWinnersTestable([1, 1]) != 1, "spec negative 7";      // neg 7 scaled: wrong 1, correct 0
  expect CountPossibleWinnersTestable([2, 2]) != 1, "spec negative 8";      // neg 8 scaled: wrong 1, correct 0
  expect CountPossibleWinnersTestable([3, 3, 3]) != 1, "spec negative 9";   // neg 9: wrong 1, correct 0
  expect CountPossibleWinnersTestable([3, 3]) != 1, "spec negative 10";     // neg 10 scaled: wrong 1, correct 0

  // ========== IMPLEMENTATION TESTS ==========
  var r1 := Arena(3, [3, 2, 2]);
  expect r1 == 1, "impl test 1a failed";
  var r2 := Arena(2, [5, 5]);
  expect r2 == 0, "impl test 1b failed";
  var r3 := Arena(4, [1, 3, 3, 7]);
  expect r3 == 3, "impl test 1c failed";

  var r4 := Arena(5, [1, 1, 1, 1, 1]);
  expect r4 == 0, "impl test 2a failed";
  var r5 := Arena(4, [1, 1, 1, 1]);
  expect r5 == 0, "impl test 2b failed";

  var r6 := Arena(6, [6, 6, 6, 6, 6, 6]);
  expect r6 == 0, "impl test 3a failed";
  var r7 := Arena(5, [6, 6, 6, 6, 6]);
  expect r7 == 0, "impl test 3b failed";

  var r8 := Arena(3, [2, 2, 2]);
  expect r8 == 0, "impl test 4a failed";
  var r9 := Arena(2, [2, 2]);
  expect r9 == 0, "impl test 4b failed";

  var r10 := Arena(5, [1, 1, 1, 1, 2]);
  expect r10 == 1, "impl test 5a failed";
  var r11 := Arena(4, [2, 2, 2, 2]);
  expect r11 == 0, "impl test 5b failed";

  var r12 := Arena(3, [90, 91, 92]);
  expect r12 == 2, "impl test 6 failed";

  var r13 := Arena(3, [1, 1, 1]);
  expect r13 == 0, "impl test 7a failed";
  var r14 := Arena(2, [1, 1]);
  expect r14 == 0, "impl test 7b failed";

  var r15 := Arena(4, [1, 1, 1, 1]);
  expect r15 == 0, "impl test 8a failed";
  var r16 := Arena(3, [1, 1, 1]);
  expect r16 == 0, "impl test 8b failed";

  var r17 := Arena(3, [3, 3, 3]);
  expect r17 == 0, "impl test 9a failed";
  var r18 := Arena(2, [3, 3]);
  expect r18 == 0, "impl test 9b failed";

  var r19 := Arena(4, [5, 5, 5, 5]);
  expect r19 == 0, "impl test 10a failed";
  var r20 := Arena(2, [5, 5]);
  expect r20 == 0, "impl test 10b failed";

  var r21 := Arena(4, [5, 5, 5, 5]);
  expect r21 == 0, "impl test 11a failed";
  var r22 := Arena(3, [5, 5, 5]);
  expect r22 == 0, "impl test 11b failed";

  var r23 := Arena(4, [1, 2, 4, 4]);
  expect r23 == 3, "impl test 12a failed";
  var r24 := Arena(2, [4, 4]);
  expect r24 == 0, "impl test 12b failed";

  var r25 := Arena(4, [1, 1, 1, 1]);
  expect r25 == 0, "impl test 13a failed";
  var r26 := Arena(2, [1, 1]);
  expect r26 == 0, "impl test 13b failed";

  var r27 := Arena(4, [2, 2, 2, 3]);
  expect r27 == 1, "impl test 14a failed";
  var r28 := Arena(2, [2, 2]);
  expect r28 == 0, "impl test 14b failed";

  var r29 := Arena(8, [1, 9, 1, 9, 8, 10, 10, 10]);
  expect r29 == 6, "impl test 15a failed";
  var r30 := Arena(5, [10, 10, 10, 10, 10]);
  expect r30 == 0, "impl test 15b failed";

  var r31 := Arena(5, [1, 1, 1, 1, 1]);
  expect r31 == 0, "impl test 16a failed";
  var r32 := Arena(3, [1, 1, 1]);
  expect r32 == 0, "impl test 16b failed";

  var r33 := Arena(3, [4, 4, 4]);
  expect r33 == 0, "impl test 17a failed";
  var r34 := Arena(2, [4, 4]);
  expect r34 == 0, "impl test 17b failed";

  var r35 := Arena(5, [9, 3, 3, 4, 100]);
  expect r35 == 3, "impl test 18a failed";
  var r36 := Arena(4, [100, 100, 100, 100]);
  expect r36 == 0, "impl test 18b failed";

  var r37 := Arena(5, [1, 2, 3, 5, 5]);
  expect r37 == 4, "impl test 19a failed";
  var r38 := Arena(3, [5, 5, 5]);
  expect r38 == 0, "impl test 19b failed";

  var r39 := Arena(4, [1, 1, 2, 2]);
  expect r39 == 2, "impl test 20a failed";
  var r40 := Arena(2, [2, 2]);
  expect r40 == 0, "impl test 20b failed";

  print "All tests passed\n";
}