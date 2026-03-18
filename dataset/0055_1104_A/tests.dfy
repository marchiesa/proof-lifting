// === Specification predicates and functions ===

function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else a[|a| - 1] + Sum(a[..|a| - 1])
}

predicate AllInRange(a: seq<int>, lo: int, hi: int)
{
  forall i | 0 <= i < |a| :: lo <= a[i] <= hi
}

function DistinctSet(a: seq<int>): set<int>
  decreases |a|
{
  if |a| == 0 then {} else {a[|a| - 1]} + DistinctSet(a[..|a| - 1])
}

function CountDistinct(a: seq<int>): int
{
  |DistinctSet(a)|
}

predicate IsValidSplitting(a: seq<int>, n: int)
{
  |a| >= 1 && AllInRange(a, 1, 9) && Sum(a) == n
}

function Pow2(e: int): int
  requires e >= 0
  ensures Pow2(e) >= 1
  decreases e
{
  if e == 0 then 1 else 2 * Pow2(e - 1)
}

function PopCount(mask: int): int
  requires mask >= 0
  ensures PopCount(mask) >= 0
  decreases mask
{
  if mask == 0 then 0 else PopCount(mask / 2) + mask % 2
}

predicate CanMakeSumFrom(n: int, mask: int, v: int)
  requires n >= 0 && mask >= 0 && 1 <= v <= 10
  decreases 10 - v
{
  if v == 10 then
    n == 0
  else if (mask / Pow2(v - 1)) % 2 == 0 then
    CanMakeSumFrom(n, mask, v + 1)
  else
    exists c | 0 <= c <= n / v :: CanMakeSumFrom(n - c * v, mask, v + 1)
}

predicate CanMakeSum(n: int, mask: int)
  requires n >= 0 && 0 <= mask < 512
{
  CanMakeSumFrom(n, mask, 1)
}

predicate CanSplitWithAtMost(n: int, d: int)
  requires n >= 0
{
  exists mask | 0 <= mask < 512 ::
    PopCount(mask) <= d && CanMakeSum(n, mask)
}

// === Method with formal specification ===

method SplitIntoDigits(n: int) returns (k: int, digits: seq<int>)
  requires n >= 1
  ensures k == |digits|
  ensures IsValidSplitting(digits, n)
  ensures !CanSplitWithAtMost(n, CountDistinct(digits) - 1)
{
  k := n;
  digits := seq(n, _ => 1);
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Test the three ensures predicates with correct small outputs.
  // All test pairs produce digits = seq(n, _ => 1), scaled to n=1,2,3.

  // Scaled from Test 1 (n=1): k=1, digits=[1]
  var d1: seq<int> := [1];
  expect 1 == |d1|, "spec pos 1: k == |digits| for n=1";
  expect IsValidSplitting(d1, 1), "spec pos 2: IsValidSplitting for n=1";
  expect !CanSplitWithAtMost(1, CountDistinct(d1) - 1), "spec pos 3: optimality for n=1";

  // Scaled from Test 2 (n=4) -> n=2: k=2, digits=[1,1]
  var d2: seq<int> := [1, 1];
  expect 2 == |d2|, "spec pos 4: k == |digits| for n=2";
  expect IsValidSplitting(d2, 2), "spec pos 5: IsValidSplitting for n=2";
  expect !CanSplitWithAtMost(2, CountDistinct(d2) - 1), "spec pos 6: optimality for n=2";

  // Scaled from Test 3 (n=27) -> n=3: k=3, digits=[1,1,1]
  var d3: seq<int> := [1, 1, 1];
  expect 3 == |d3|, "spec pos 7: k == |digits| for n=3";
  expect IsValidSplitting(d3, 3), "spec pos 8: IsValidSplitting for n=3";
  expect !CanSplitWithAtMost(3, CountDistinct(d3) - 1), "spec pos 9: optimality for n=3";

  // === SPEC NEGATIVE TESTS ===
  // Negative pairs corrupt k to n+1 while digits stay the same.
  // The ensures "k == |digits|" is violated: wrong_k != |digits|.

  // Scaled from Neg 1 (n=1, wrong k=2, digits=[1])
  expect !(2 == |d1|), "spec neg 1: wrong k=2 for n=1";
  // Scaled from Neg 2 (n=4 -> n=2, wrong k=3, digits=[1,1])
  expect !(3 == |d2|), "spec neg 2: wrong k=3 for n=2";
  // Scaled from Neg 3 (n=27 -> n=3, wrong k=4, digits=[1,1,1])
  expect !(4 == |d3|), "spec neg 3: wrong k=4 for n=3";
  // Scaled from Neg 4 (n=1000 -> n=1, wrong k=2, digits=[1])
  expect !(2 == |d1|), "spec neg 4: wrong k=2 for n=1";
  // Scaled from Neg 5 (n=239 -> n=2, wrong k=3, digits=[1,1])
  expect !(3 == |d2|), "spec neg 5: wrong k=3 for n=2";
  // Scaled from Neg 6 (n=997 -> n=3, wrong k=4, digits=[1,1,1])
  expect !(4 == |d3|), "spec neg 6: wrong k=4 for n=3";
  // Scaled from Neg 7 (n=998 -> n=1, wrong k=2, digits=[1])
  expect !(2 == |d1|), "spec neg 7: wrong k=2 for n=1";
  // Scaled from Neg 8 (n=993 -> n=3, wrong k=4, digits=[1,1,1])
  expect !(4 == |d3|), "spec neg 8: wrong k=4 for n=3";
  // Scaled from Neg 9 (n=988 -> n=2, wrong k=3, digits=[1,1])
  expect !(3 == |d2|), "spec neg 9: wrong k=3 for n=2";
  // Scaled from Neg 10 (n=995 -> n=1, wrong k=2, digits=[1])
  expect !(2 == |d1|), "spec neg 10: wrong k=2 for n=1";

  // === IMPLEMENTATION TESTS ===
  var k: int;
  var digits: seq<int>;

  // Test 1: n=1
  k, digits := SplitIntoDigits(1);
  expect k == 1, "impl 1: k mismatch";
  expect digits == seq(1, _ => 1), "impl 1: digits mismatch";

  // Test 2: n=4
  k, digits := SplitIntoDigits(4);
  expect k == 4, "impl 2: k mismatch";
  expect digits == seq(4, _ => 1), "impl 2: digits mismatch";

  // Test 3: n=27
  k, digits := SplitIntoDigits(27);
  expect k == 27, "impl 3: k mismatch";
  expect digits == seq(27, _ => 1), "impl 3: digits mismatch";

  // Test 4: n=1000
  k, digits := SplitIntoDigits(1000);
  expect k == 1000, "impl 4: k mismatch";
  expect digits == seq(1000, _ => 1), "impl 4: digits mismatch";

  // Test 5: n=239
  k, digits := SplitIntoDigits(239);
  expect k == 239, "impl 5: k mismatch";
  expect digits == seq(239, _ => 1), "impl 5: digits mismatch";

  // Test 6: n=997
  k, digits := SplitIntoDigits(997);
  expect k == 997, "impl 6: k mismatch";
  expect digits == seq(997, _ => 1), "impl 6: digits mismatch";

  // Test 7: n=998
  k, digits := SplitIntoDigits(998);
  expect k == 998, "impl 7: k mismatch";
  expect digits == seq(998, _ => 1), "impl 7: digits mismatch";

  // Test 8: n=993
  k, digits := SplitIntoDigits(993);
  expect k == 993, "impl 8: k mismatch";
  expect digits == seq(993, _ => 1), "impl 8: digits mismatch";

  // Test 9: n=988
  k, digits := SplitIntoDigits(988);
  expect k == 988, "impl 9: k mismatch";
  expect digits == seq(988, _ => 1), "impl 9: digits mismatch";

  // Test 10: n=995
  k, digits := SplitIntoDigits(995);
  expect k == 995, "impl 10: k mismatch";
  expect digits == seq(995, _ => 1), "impl 10: digits mismatch";

  // Test 11: n=996
  k, digits := SplitIntoDigits(996);
  expect k == 996, "impl 11: k mismatch";
  expect digits == seq(996, _ => 1), "impl 11: digits mismatch";

  // Test 12: n=994
  k, digits := SplitIntoDigits(994);
  expect k == 994, "impl 12: k mismatch";
  expect digits == seq(994, _ => 1), "impl 12: digits mismatch";

  // Test 13: n=992
  k, digits := SplitIntoDigits(992);
  expect k == 992, "impl 13: k mismatch";
  expect digits == seq(992, _ => 1), "impl 13: digits mismatch";

  // Test 14: n=999
  k, digits := SplitIntoDigits(999);
  expect k == 999, "impl 14: k mismatch";
  expect digits == seq(999, _ => 1), "impl 14: digits mismatch";

  // Test 15: n=191
  k, digits := SplitIntoDigits(191);
  expect k == 191, "impl 15: k mismatch";
  expect digits == seq(191, _ => 1), "impl 15: digits mismatch";

  // Test 16: n=94
  k, digits := SplitIntoDigits(94);
  expect k == 94, "impl 16: k mismatch";
  expect digits == seq(94, _ => 1), "impl 16: digits mismatch";

  // Test 17: n=57
  k, digits := SplitIntoDigits(57);
  expect k == 57, "impl 17: k mismatch";
  expect digits == seq(57, _ => 1), "impl 17: digits mismatch";

  // Test 18: n=748
  k, digits := SplitIntoDigits(748);
  expect k == 748, "impl 18: k mismatch";
  expect digits == seq(748, _ => 1), "impl 18: digits mismatch";

  // Test 19: n=485
  k, digits := SplitIntoDigits(485);
  expect k == 485, "impl 19: k mismatch";
  expect digits == seq(485, _ => 1), "impl 19: digits mismatch";

  // Test 20: n=78
  k, digits := SplitIntoDigits(78);
  expect k == 78, "impl 20: k mismatch";
  expect digits == seq(78, _ => 1), "impl 20: digits mismatch";

  print "All tests passed\n";
}