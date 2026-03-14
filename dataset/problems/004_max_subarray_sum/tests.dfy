// Maximum Subarray Sum -- Runtime spec tests

function SumSeq(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + SumSeq(a, lo + 1, hi)
}

// Compilable version of IsMaxSubarraySum using bounded quantifiers
predicate IsMaxSubarraySum(a: seq<int>, s: int)
  requires |a| > 0
{
  (exists lo, hi | 0 <= lo < hi <= |a| :: SumSeq(a, lo, hi) == s) &&
  (forall lo, hi | 0 <= lo < hi <= |a| :: SumSeq(a, lo, hi) <= s)
}

method Main()
{
  // Test SumSeq
  var a1 := [1, 2, 3, 4];
  expect SumSeq(a1, 0, 4) == 10, "sum of [1,2,3,4] should be 10";
  expect SumSeq(a1, 0, 0) == 0, "empty range sum should be 0";
  expect SumSeq(a1, 1, 3) == 5, "sum of [2,3] should be 5";
  expect SumSeq(a1, 0, 1) == 1, "sum of [1] should be 1";

  // Test IsMaxSubarraySum - classic example [-2, 1, -3, 4, -1, 2, 1, -5, 4]
  var a2 := [-2, 1, -3, 4, -1, 2, 1, -5, 4];
  expect IsMaxSubarraySum(a2, 6), "max subarray sum of classic example should be 6";
  expect !IsMaxSubarraySum(a2, 5), "5 is not the max subarray sum";
  expect !IsMaxSubarraySum(a2, 7), "7 is not achievable as a subarray sum";

  // Test single element
  var a3 := [5];
  expect IsMaxSubarraySum(a3, 5), "single element [5] max is 5";
  expect !IsMaxSubarraySum(a3, 4), "4 is not max for [5]";

  // Test single negative element
  var a4 := [-3];
  expect IsMaxSubarraySum(a4, -3), "single element [-3] max is -3";
  expect !IsMaxSubarraySum(a4, 0), "0 is not achievable for [-3]";

  // Test all positive
  var a5 := [1, 2, 3];
  expect IsMaxSubarraySum(a5, 6), "sum of entire [1,2,3] is max = 6";
  expect !IsMaxSubarraySum(a5, 3), "3 is not the max for [1,2,3]";

  // Test all negative
  var a6 := [-5, -2, -8];
  expect IsMaxSubarraySum(a6, -2), "max subarray of all negatives is least negative = -2";
  expect !IsMaxSubarraySum(a6, -5), "-5 is not the max (it's worse than -2)";

  print "All spec tests passed\n";
}
