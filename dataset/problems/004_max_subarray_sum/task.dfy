// Maximum Subarray Sum (Kadane's Algorithm)
// Task: Add loop invariants so that Dafny can verify this program.

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
  // s is achievable: there exist lo, hi with sum == s
  (exists lo, hi :: 0 <= lo < hi <= |a| && SumSeq(a, lo, hi) == s) &&
  // s is maximal: no subarray has a larger sum
  (forall lo, hi :: 0 <= lo < hi <= |a| ==> SumSeq(a, lo, hi) <= s)
}

method MaxSubarraySum(a: seq<int>) returns (maxSum: int)
  requires |a| > 0
  ensures IsMaxSubarraySum(a, maxSum)
{
  maxSum := a[0];
  var currentSum := a[0];
  var bestLo, bestHi := 0, 1;
  var curLo := 0;
  var i := 1;
  while i < |a|
  {
    if currentSum + a[i] > a[i] {
      currentSum := currentSum + a[i];
    } else {
      currentSum := a[i];
      curLo := i;
    }
    if currentSum > maxSum {
      maxSum := currentSum;
      bestLo := curLo;
      bestHi := i + 1;
    }
    i := i + 1;
  }
}
