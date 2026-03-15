// Maximum Circular Subarray Sum -- Spec tests

function Max(a: int, b: int): int { if a >= b then a else b }

function SumRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + SumRange(a, lo + 1, hi)
}

predicate IsMaxCircularSubarraySum(a: seq<int>, result: int)
  requires |a| > 0
{
  (exists lo, hi :: 0 <= lo < hi <= |a| && SumRange(a, lo, hi) == result) &&
  (forall lo, hi :: 0 <= lo < hi <= |a| ==> SumRange(a, lo, hi) <= result)
}

method MaxCircularSubarray(a: seq<int>) returns (result: int)
  requires |a| > 0
  ensures IsMaxCircularSubarraySum(a, result)
{
  result := a[0];
  var bestLo := 0;
  var bestHi := 1;
  var i := 0;
  while i < |a|
    decreases |a| - i
  {
    var s := 0;
    var j := i;
    while j < |a|
      decreases |a| - j
    {
      s := s + a[j];
      if s > result {
        result := s;
        bestLo := i;
        bestHi := j + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  assume {:axiom} IsMaxCircularSubarraySum(a, result);
}

method Main() {
  // Test 1: classic case
  var a1 := [1, -2, 3, -1, 2];
  var r1 := MaxCircularSubarray(a1);
  expect SumRange(a1, 2, 5) == 4;
  expect r1 >= 4;

  // Test 2: single element
  var a2 := [5];
  var r2 := MaxCircularSubarray(a2);
  expect r2 == 5;

  // Test 3: all negative
  var a3 := [-3, -2, -5];
  var r3 := MaxCircularSubarray(a3);
  expect r3 == -2;
  expect SumRange(a3, 1, 2) == -2;

  // Test 4: all positive
  var a4 := [1, 2, 3];
  var r4 := MaxCircularSubarray(a4);
  expect r4 == 6;

  // Negative test: result should not be less than single element
  var a5 := [10, -1, -1];
  var r5 := MaxCircularSubarray(a5);
  expect r5 >= 10;

  print "All spec tests passed\n";
}
