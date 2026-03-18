function Sum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s|-1]) + s[|s|-1]
}

predicate AllNonNeg(s: seq<int>)
{
  forall i | 0 <= i < |s| :: s[i] >= 0
}

predicate CanAchieveExtra(piles: seq<int>, budget: int, extra: int)
  decreases |piles|
{
  if extra < 0 || budget < 0 then false
  else if |piles| == 0 then extra == 0
  else
    exists take | 0 <= take <= piles[|piles| - 1] ::
      take * |piles| <= budget
      && CanAchieveExtra(piles[..|piles| - 1], budget - take * |piles|, extra - take)
}

predicate IsOptimal(a: seq<int>, d: int, result: int)
  requires |a| > 0
{
  var piles := a[1..];
  var extra := result - a[0];
  var maxExtra := Sum(piles);
  0 <= extra
  && CanAchieveExtra(piles, d, extra)
  && (forall v | extra < v <= maxExtra :: !CanAchieveExtra(piles, d, v))
}

method CowAndHaybales(a: seq<int>, d: int) returns (result: int)
  requires |a| > 0
  requires d >= 0
  requires AllNonNeg(a)
  ensures IsOptimal(a, d, result)
{
  var n := |a|;
  var arr := new int[n];
  var Asum := 0;
  for k := 0 to n {
    arr[k] := a[k];
    Asum := Asum + a[k];
  }
  var remaining := d;
  while remaining > 0 && arr[0] != Asum
    decreases remaining
  {
    var i := 1;
    while i < n && arr[i] == 0
      decreases n - i
    {
      i := i + 1;
    }
    if i < n {
      arr[i - 1] := arr[i - 1] + 1;
      arr[i] := arr[i] - 1;
    }
    remaining := remaining - 1;
  }
  result := arr[0];
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Small inputs to keep bounded quantifier enumeration fast

  // Spec positive 1: single pile, no moves possible
  expect IsOptimal([3], 5, 3), "spec positive 1";

  // Spec positive 2: single pile with 0
  expect IsOptimal([0], 1, 0), "spec positive 2";

  // Spec positive 3: no budget, result = a[0]
  expect IsOptimal([1, 2, 3], 0, 1), "spec positive 3";

  // Spec positive 4: move 1 bale from distance 1
  expect IsOptimal([0, 3], 1, 1), "spec positive 4";

  // Spec positive 5: move all 3 bales from distance 1
  expect IsOptimal([0, 3], 3, 3), "spec positive 5";

  // Spec positive 6: move everything to pile 0
  expect IsOptimal([1, 1, 1], 5, 3), "spec positive 6";

  // Spec positive 7: bales at distance 2, each costs 2 moves, can afford 1
  expect IsOptimal([0, 0, 3], 3, 1), "spec positive 7";

  // ===== SPEC NEGATIVE TESTS =====
  // Small inputs with wrong outputs that the spec should reject

  // Spec negative 1: wrong=4, correct=3 (off by +1)
  expect !IsOptimal([3], 5, 4), "spec negative 1";

  // Spec negative 2: wrong=1, correct=0 (off by +1)
  expect !IsOptimal([0], 1, 1), "spec negative 2";

  // Spec negative 3: wrong=2, correct=1 (off by +1, no budget)
  expect !IsOptimal([1, 2, 3], 0, 2), "spec negative 3";

  // Spec negative 4: wrong=2, correct=1 (off by +1)
  expect !IsOptimal([0, 3], 1, 2), "spec negative 4";

  // Spec negative 5: wrong=4, correct=3 (exceeds what's available)
  expect !IsOptimal([1, 1, 1], 5, 4), "spec negative 5";

  // Spec negative 6: wrong=2, correct=1 (off by +1)
  expect !IsOptimal([0, 0, 3], 3, 2), "spec negative 6";

  // Spec negative 7: wrong=4, correct=3 (exceeds total)
  expect !IsOptimal([0, 3], 3, 4), "spec negative 7";

  // ===== IMPLEMENTATION TESTS =====

  var r1 := CowAndHaybales([1, 0, 3, 2], 5);
  expect r1 == 3, "impl test 1 failed";

  var r2 := CowAndHaybales([100, 1], 2);
  expect r2 == 101, "impl test 2 failed";

  var r3 := CowAndHaybales([0], 8);
  expect r3 == 0, "impl test 3 failed";

  var r4 := CowAndHaybales([5, 3, 2], 10);
  expect r4 == 10, "impl test 4 failed";

  var r5 := CowAndHaybales([7], 5);
  expect r5 == 7, "impl test 5 failed";

  var r6 := CowAndHaybales([0, 0, 0, 0, 10], 3);
  expect r6 == 0, "impl test 6 failed";

  var r7 := CowAndHaybales([0, 50], 1);
  expect r7 == 1, "impl test 7 failed";

  var r8 := CowAndHaybales([1, 1, 1, 1], 20);
  expect r8 == 4, "impl test 8 failed";

  var r9 := CowAndHaybales([10, 20, 30], 0);
  expect r9 == 10, "impl test 9 failed";

  var r10 := CowAndHaybales([0], 1);
  expect r10 == 0, "impl test 10 failed";

  var r11 := CowAndHaybales([2, 4, 3], 6);
  expect r11 == 7, "impl test 11 failed";

  var r12 := CowAndHaybales([0, 0], 100);
  expect r12 == 0, "impl test 12 failed";

  var r13 := CowAndHaybales([10, 10, 10, 10, 10], 50);
  expect r13 == 36, "impl test 13 failed";

  var r14 := CowAndHaybales([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], 5);
  expect r14 == 3, "impl test 14 failed";

  print "All tests passed\n";
}