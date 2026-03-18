function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

predicate BitSet(mask: nat, i: nat)
{
  (mask / Pow2(i)) % 2 == 1
}

function SubseqProduct(a: seq<int>, mask: nat): int
  decreases |a|
{
  if |a| == 0 then 1
  else if BitSet(mask, |a| - 1) then SubseqProduct(a[..|a|-1], mask) * a[|a|-1]
  else SubseqProduct(a[..|a|-1], mask)
}

predicate IsPerfectSquare(x: int)
{
  x >= 0 && exists s | 0 <= s <= x :: s * s == x
}

predicate HasNonPerfectSquareSubseqProduct(a: seq<int>)
{
  exists mask: nat | 1 <= mask < Pow2(|a|) :: !IsPerfectSquare(SubseqProduct(a, mask))
}

method PerfectlyImperfectArray(a: seq<int>) returns (result: bool)
  ensures result == HasNonPerfectSquareSubseqProduct(a)
{
  result := false;
  var i := 0;
  while i < |a|
  {
    var x := a[i];
    var s := 0;
    while s * s < x
    {
      s := s + 1;
    }
    if s * s != x {
      result := true;
      return;
    }
    i := i + 1;
  }
}

method Main()
{
  // ============================================================
  // SPEC POSITIVE TESTS (small inputs, testing the ensures predicate)
  // ============================================================
  expect HasNonPerfectSquareSubseqProduct([1]) == false, "spec positive 1";
  expect HasNonPerfectSquareSubseqProduct([2]) == true, "spec positive 2";
  expect HasNonPerfectSquareSubseqProduct([3]) == true, "spec positive 3";
  expect HasNonPerfectSquareSubseqProduct([5]) == true, "spec positive 4";
  expect HasNonPerfectSquareSubseqProduct([1, 5, 4]) == true, "spec positive 5";
  expect HasNonPerfectSquareSubseqProduct([3, 3]) == true, "spec positive 6";
  expect HasNonPerfectSquareSubseqProduct([2, 2]) == true, "spec positive 7";
  expect HasNonPerfectSquareSubseqProduct([4, 4]) == false, "spec positive 8";
  expect HasNonPerfectSquareSubseqProduct([1, 1, 1]) == false, "spec positive 9";
  expect HasNonPerfectSquareSubseqProduct([4, 4, 4]) == false, "spec positive 10";

  // ============================================================
  // SPEC NEGATIVE TESTS (small inputs, wrong outputs must be rejected)
  // ============================================================
  // Neg 3 scaled: [3,3,3,3,3]->wrong=false => [3]->wrong=false
  expect HasNonPerfectSquareSubseqProduct([3]) != false, "spec negative 1";
  // Neg 9: [5]->wrong=false
  expect HasNonPerfectSquareSubseqProduct([5]) != false, "spec negative 2";
  // Neg 6: [2,2]->wrong=false
  expect HasNonPerfectSquareSubseqProduct([2, 2]) != false, "spec negative 3";
  // Neg 1 scaled: [100,10000]->correct=false,wrong=true => [4,4]->wrong=true
  expect HasNonPerfectSquareSubseqProduct([4, 4]) != true, "spec negative 4";
  // Neg 5 scaled: [7,7,28]->wrong=false => [3,3]->wrong=false
  expect HasNonPerfectSquareSubseqProduct([3, 3]) != false, "spec negative 5";
  // Neg 4 scaled: [12,4,3]->wrong=false => [3,4,1]->wrong=false
  expect HasNonPerfectSquareSubseqProduct([3, 4, 1]) != false, "spec negative 6";
  // Neg 10 scaled: [6]->wrong=false => [2]->wrong=false
  expect HasNonPerfectSquareSubseqProduct([2]) != false, "spec negative 7";

  // ============================================================
  // IMPLEMENTATION TESTS (full-size inputs, testing the method)
  // ============================================================
  // Test 1
  var r1 := PerfectlyImperfectArray([1, 5, 4]);
  expect r1 == true, "impl test 1a failed";
  var r2 := PerfectlyImperfectArray([100, 10000]);
  expect r2 == false, "impl test 1b failed";

  // Test 2
  var r3 := PerfectlyImperfectArray([1]);
  expect r3 == false, "impl test 2a failed";
  var r4 := PerfectlyImperfectArray([2]);
  expect r4 == true, "impl test 2b failed";
  var r5 := PerfectlyImperfectArray([3]);
  expect r5 == true, "impl test 2c failed";

  // Test 3
  var r6 := PerfectlyImperfectArray([3, 3, 3, 3, 3]);
  expect r6 == true, "impl test 3 failed";

  // Test 4
  var r7 := PerfectlyImperfectArray([3, 12]);
  expect r7 == true, "impl test 4a failed";
  var r8 := PerfectlyImperfectArray([3, 3]);
  expect r8 == true, "impl test 4b failed";
  var r9 := PerfectlyImperfectArray([12, 4, 3]);
  expect r9 == true, "impl test 4c failed";

  // Test 5
  var r10 := PerfectlyImperfectArray([7, 7, 28]);
  expect r10 == true, "impl test 5 failed";

  // Test 6
  var r11 := PerfectlyImperfectArray([2, 2]);
  expect r11 == true, "impl test 6 failed";

  // Test 7
  var r12 := PerfectlyImperfectArray([1412, 1412]);
  expect r12 == true, "impl test 7 failed";

  // Test 8
  var r13 := PerfectlyImperfectArray([3]);
  expect r13 == true, "impl test 8 failed";

  // Test 9
  var r14 := PerfectlyImperfectArray([5]);
  expect r14 == true, "impl test 9 failed";

  // Test 10
  var r15 := PerfectlyImperfectArray([6]);
  expect r15 == true, "impl test 10 failed";

  // Test 11
  var r16 := PerfectlyImperfectArray([1412]);
  expect r16 == true, "impl test 11 failed";

  // Test 12
  var r17 := PerfectlyImperfectArray([3, 12]);
  expect r17 == true, "impl test 12a failed";
  var r18 := PerfectlyImperfectArray([8, 2]);
  expect r18 == true, "impl test 12b failed";
  var r19 := PerfectlyImperfectArray([12, 4, 3]);
  expect r19 == true, "impl test 12c failed";

  // Test 13
  var r20 := PerfectlyImperfectArray([3, 3]);
  expect r20 == true, "impl test 13a failed";
  var r21 := PerfectlyImperfectArray([1, 1, 1, 1, 1]);
  expect r21 == false, "impl test 13b failed";
  var r22 := PerfectlyImperfectArray([1, 1, 1, 1, 1, 1]);
  expect r22 == false, "impl test 13c failed";
  var r23 := PerfectlyImperfectArray([2, 2, 4, 4, 4]);
  expect r23 == true, "impl test 13d failed";
  var r24 := PerfectlyImperfectArray([4, 4, 4, 4, 4]);
  expect r24 == false, "impl test 13e failed";

  // Test 14
  var r25 := PerfectlyImperfectArray([7]);
  expect r25 == true, "impl test 14 failed";

  // Test 15
  var r26 := PerfectlyImperfectArray([1]);
  expect r26 == false, "impl test 15a failed";
  var r27 := PerfectlyImperfectArray([2]);
  expect r27 == true, "impl test 15b failed";

  // Test 16
  var r28 := PerfectlyImperfectArray([6, 6]);
  expect r28 == true, "impl test 16 failed";

  // Test 17
  var r29 := PerfectlyImperfectArray([3, 2, 1, 1, 1]);
  expect r29 == true, "impl test 17 failed";

  // Test 18
  var r30 := PerfectlyImperfectArray([2, 8]);
  expect r30 == true, "impl test 18 failed";

  // Test 19
  var r31 := PerfectlyImperfectArray([3, 3]);
  expect r31 == true, "impl test 19 failed";

  // Test 20
  var r32 := PerfectlyImperfectArray([2]);
  expect r32 == true, "impl test 20 failed";

  print "All tests passed\n";
}