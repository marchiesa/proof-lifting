predicate IsGood(a: seq<int>)
{
  forall i | 0 <= i < |a| :: i % 2 == a[i] % 2
}

function SwapElems(a: seq<int>, p: int, q: int): seq<int>
  requires 0 <= p < |a|
  requires 0 <= q < |a|
{
  a[p := a[q]][q := a[p]]
}

predicate ReachableGoodIn(a: seq<int>, steps: nat)
  decreases steps
{
  if steps == 0 then IsGood(a)
  else IsGood(a) || exists p: int, q: int | 0 <= p < q < |a| ::
    ReachableGoodIn(SwapElems(a, p, q), steps - 1)
}

// Bundles all ensures conditions into one testable predicate
predicate ValidResult(a: seq<int>, result: int)
{
  if result == -1 then !ReachableGoodIn(a, |a| / 2)
  else if result == 0 then ReachableGoodIn(a, 0)
  else if result >= 1 then ReachableGoodIn(a, result) && !ReachableGoodIn(a, result - 1)
  else false
}

method EvenArray(a: seq<int>) returns (result: int)
  requires forall i | 0 <= i < |a| :: a[i] >= 0
  ensures result == -1 || result >= 0
  ensures result >= 0 ==> ReachableGoodIn(a, result)
  ensures result >= 1 ==> !ReachableGoodIn(a, result - 1)
  ensures result == -1 ==> !ReachableGoodIn(a, |a| / 2)
{
  var odd_at_even := 0;
  var even_at_odd := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
  {
    if i % 2 == 0 && a[i] % 2 != 0 {
      odd_at_even := odd_at_even + 1;
    } else if i % 2 != 0 && a[i] % 2 == 0 {
      even_at_odd := even_at_odd + 1;
    }
    i := i + 1;
  }
  if odd_at_even == even_at_odd {
    result := odd_at_even;
  } else {
    result := -1;
  }
}

method Main() {
  // ===== SPEC POSITIVE TESTS =====
  // Small inputs (length 1-3, values 0-5) with correct outputs

  // From Test 2/6: [0] -> 0 (single even elem at even index, already good)
  expect ValidResult([0], 0), "spec positive 1";

  // From Test 1c/5a scaled: [7]->{-1} scaled to [1] -> -1 (odd at even index, impossible)
  expect ValidResult([1], -1), "spec positive 2";

  // From Test 5b: [4,3] -> 0 (already good)
  expect ValidResult([4, 3], 0), "spec positive 3";

  // From Test 1b scaled: [3,2,6]->1 scaled to [1,0,2] -> 1 (one swap needed)
  expect ValidResult([1, 0, 2], 1), "spec positive 4";

  // From Test 10: [2,1,0] -> 0 (already good)
  expect ValidResult([2, 1, 0], 0), "spec positive 5";

  // From Test 5c: [1,2,3] -> -1 (2 odd-at-even, 1 even-at-odd, impossible)
  expect ValidResult([1, 2, 3], -1), "spec positive 6";

  // From Test 3/9 scaled: [0,1,2] -> 0 (already good)
  expect ValidResult([0, 1, 2], 0), "spec positive 7";

  // From Test 7 scaled: [1,3,5,7,9]->{-1} scaled to [1,3,5] -> -1 (all odd, impossible)
  expect ValidResult([1, 3, 5], -1), "spec positive 8";

  // ===== SPEC NEGATIVE TESTS =====
  // Small inputs with WRONG outputs that the spec should reject

  // From Neg 2/6: [0] wrong=1 (already good, claiming 1 swap is wrong)
  expect !ValidResult([0], 1), "spec negative 1";

  // From Neg 3/9 scaled: [0,1,2] wrong=1 (already good, 1 is wrong)
  expect !ValidResult([0, 1, 2], 1), "spec negative 2";

  // From Neg 5 scaled: [7] wrong=0 scaled to [1] wrong=0 (not good, 0 is wrong)
  expect !ValidResult([1], 0), "spec negative 3";

  // From Neg 7 scaled: [1,3,5,7,9] wrong=0 scaled to [1,3,5] wrong=0
  expect !ValidResult([1, 3, 5], 0), "spec negative 4";

  // From Neg 8 scaled: [2,4,6,8,10,12] wrong=0 scaled to [2,4] wrong=0
  expect !ValidResult([2, 4], 0), "spec negative 5";

  // From Neg 10: [2,1,0] wrong=1 (already good, 1 is wrong)
  expect !ValidResult([2, 1, 0], 1), "spec negative 6";

  // ===== IMPLEMENTATION TESTS =====

  // Test 1: [3,2,7,6]->2, [3,2,6]->1, [7]->-1, [4,9,2,1,18,3,0]->0
  var r1a := EvenArray([3, 2, 7, 6]);
  expect r1a == 2, "impl test 1a failed";
  var r1b := EvenArray([3, 2, 6]);
  expect r1b == 1, "impl test 1b failed";
  var r1c := EvenArray([7]);
  expect r1c == -1, "impl test 1c failed";
  var r1d := EvenArray([4, 9, 2, 1, 18, 3, 0]);
  expect r1d == 0, "impl test 1d failed";

  // Test 2: seven [0]->0
  var r2a := EvenArray([0]);
  expect r2a == 0, "impl test 2a failed";
  var r2b := EvenArray([0]);
  expect r2b == 0, "impl test 2b failed";
  var r2c := EvenArray([0]);
  expect r2c == 0, "impl test 2c failed";
  var r2d := EvenArray([0]);
  expect r2d == 0, "impl test 2d failed";
  var r2e := EvenArray([0]);
  expect r2e == 0, "impl test 2e failed";
  var r2f := EvenArray([0]);
  expect r2f == 0, "impl test 2f failed";
  var r2g := EvenArray([0]);
  expect r2g == 0, "impl test 2g failed";

  // Test 3: [0,5,2,1]->0
  var r3 := EvenArray([0, 5, 2, 1]);
  expect r3 == 0, "impl test 3 failed";

  // Test 4: [3,2,7,6]->2
  var r4 := EvenArray([3, 2, 7, 6]);
  expect r4 == 2, "impl test 4 failed";

  // Test 5: [7]->-1, [4,3]->0, [1,2,3]->-1
  var r5a := EvenArray([7]);
  expect r5a == -1, "impl test 5a failed";
  var r5b := EvenArray([4, 3]);
  expect r5b == 0, "impl test 5b failed";
  var r5c := EvenArray([1, 2, 3]);
  expect r5c == -1, "impl test 5c failed";

  // Test 6: [0]->0
  var r6 := EvenArray([0]);
  expect r6 == 0, "impl test 6 failed";

  // Test 7: [1,3,5,7,9]->-1
  var r7 := EvenArray([1, 3, 5, 7, 9]);
  expect r7 == -1, "impl test 7 failed";

  // Test 8: [2,4,6,8,10,12]->-1, [1,3,5,7,9,11]->-1
  var r8a := EvenArray([2, 4, 6, 8, 10, 12]);
  expect r8a == -1, "impl test 8a failed";
  var r8b := EvenArray([1, 3, 5, 7, 9, 11]);
  expect r8b == -1, "impl test 8b failed";

  // Test 9: [0,1,2,3,4,5,6,7]->0
  var r9 := EvenArray([0, 1, 2, 3, 4, 5, 6, 7]);
  expect r9 == 0, "impl test 9 failed";

  // Test 10: [2,1,0]->0
  var r10 := EvenArray([2, 1, 0]);
  expect r10 == 0, "impl test 10 failed";

  print "All tests passed\n";
}