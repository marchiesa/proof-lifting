// Maximum Subarray Sum -- Test cases

function SumSeq(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + SumSeq(a, lo + 1, hi)
}

predicate IsMaxSubarraySum(a: seq<int>, s: int)
  requires |a| > 0
{
  (exists lo, hi :: 0 <= lo < hi <= |a| && SumSeq(a, lo, hi) == s) &&
  (forall lo, hi :: 0 <= lo < hi <= |a| ==> SumSeq(a, lo, hi) <= s)
}

method {:axiom} MaxSubarraySum(a: seq<int>) returns (maxSum: int)
  requires |a| > 0
  ensures IsMaxSubarraySum(a, maxSum)

method TestClassic()
{
  var a := [-2, 1, -3, 4, -1, 2, 1, -5, 4];
  var s := MaxSubarraySum(a);
  // maxSum should be 6
}

method TestSinglePositive()
{
  var a := [5];
  var s := MaxSubarraySum(a);
  assert SumSeq(a, 0, 1) == 5;
}

method TestSingleNegative()
{
  var a := [-3];
  var s := MaxSubarraySum(a);
  assert SumSeq(a, 0, 1) == -3;
}

method TestAllPositive()
{
  var a := [1, 2, 3];
  var s := MaxSubarraySum(a);
  // should be 6
}

method TestAllNegative()
{
  var a := [-5, -2, -8];
  var s := MaxSubarraySum(a);
  // should be -2, the least negative
  assert SumSeq(a, 1, 2) == -2;
}
