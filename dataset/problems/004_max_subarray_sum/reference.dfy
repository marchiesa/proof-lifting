// Maximum Subarray Sum (Kadane's Algorithm) -- Reference solution with invariants

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

lemma SumSeqExtend(a: seq<int>, lo: int, hi: int)
  requires 0 <= lo < hi <= |a|
  ensures SumSeq(a, lo, hi) == SumSeq(a, lo, hi - 1) + a[hi - 1]
  decreases hi - lo
{
  if lo == hi - 1 {
    assert SumSeq(a, lo, hi) == a[lo] + SumSeq(a, lo + 1, hi);
    assert SumSeq(a, lo + 1, hi) == 0;
    assert SumSeq(a, lo, hi - 1) == 0;
  } else {
    SumSeqExtend(a, lo + 1, hi);
    assert SumSeq(a, lo, hi) == a[lo] + SumSeq(a, lo + 1, hi);
    assert SumSeq(a, lo, hi - 1) == a[lo] + SumSeq(a, lo + 1, hi - 1);
  }
}

lemma MaxEndingHereExtend(a: seq<int>, i: int, curSum: int, curLo: int)
  requires 0 < i < |a|
  requires 0 <= curLo < i
  requires SumSeq(a, curLo, i) == curSum
  requires forall lo :: 0 <= lo < i ==> SumSeq(a, lo, i) <= curSum
  ensures var newSum := if curSum + a[i] > a[i] then curSum + a[i] else a[i];
          var newLo := if curSum + a[i] > a[i] then curLo else i;
          SumSeq(a, newLo, i + 1) == newSum &&
          (forall lo {:trigger SumSeq(a, lo, i + 1)} :: 0 <= lo < i + 1 ==> SumSeq(a, lo, i + 1) <= newSum)
{
  forall lo {:trigger SumSeq(a, lo, i + 1)} | 0 <= lo < i + 1
    ensures SumSeq(a, lo, i + 1) <= (if curSum + a[i] > a[i] then curSum + a[i] else a[i])
  {
    SumSeqExtend(a, lo, i + 1);
    assert SumSeq(a, lo, i + 1) == SumSeq(a, lo, i) + a[i];
    if lo < i {
      assert SumSeq(a, lo, i) <= curSum;
      assert SumSeq(a, lo, i + 1) <= curSum + a[i];
    }
  }
  SumSeqExtend(a, curLo, i + 1);
  if curSum + a[i] > a[i] {
  } else {
    SumSeqExtend(a, i, i + 1);
  }
}

method MaxSubarraySum(a: seq<int>) returns (maxSum: int)
  requires |a| > 0
  ensures IsMaxSubarraySum(a, maxSum)
{
  maxSum := a[0];
  var currentSum := a[0];
  var bestLo, bestHi := 0, 1;
  var curLo := 0;

  assert SumSeq(a, 0, 1) == a[0] + SumSeq(a, 1, 1) == a[0];

  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant 0 <= curLo < i
    invariant 0 <= bestLo < bestHi <= i
    invariant SumSeq(a, curLo, i) == currentSum
    invariant forall lo :: 0 <= lo < i ==> SumSeq(a, lo, i) <= currentSum
    invariant SumSeq(a, bestLo, bestHi) == maxSum
    invariant forall lo, hi :: 0 <= lo < hi <= i ==> SumSeq(a, lo, hi) <= maxSum
    decreases |a| - i
  {
    MaxEndingHereExtend(a, i, currentSum, curLo);
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
    assert forall lo, hi :: 0 <= lo < hi <= i + 1 ==> SumSeq(a, lo, hi) <= maxSum by {
      forall lo, hi | 0 <= lo < hi <= i + 1
        ensures SumSeq(a, lo, hi) <= maxSum
      {
        if hi <= i {
          // Already known from invariant maintained at previous iteration
        } else {
          assert hi == i + 1;
          // We know SumSeq(a, lo, i+1) <= currentSum <= maxSum
        }
      }
    }
    i := i + 1;
  }
}
