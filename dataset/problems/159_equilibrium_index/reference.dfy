// Find Equilibrium Index -- Reference solution with invariants

function SumRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + SumRange(a, lo + 1, hi)
}

predicate IsEquilibrium(a: seq<int>, idx: int) {
  0 <= idx < |a| &&
  SumRange(a, 0, idx) == SumRange(a, idx + 1, |a|)
}

predicate NoEquilibrium(a: seq<int>) {
  forall i :: 0 <= i < |a| ==> !IsEquilibrium(a, i)
}

lemma SumRangeSplit(a: seq<int>, lo: int, mid: int, hi: int)
  requires 0 <= lo <= mid <= hi <= |a|
  ensures SumRange(a, lo, hi) == SumRange(a, lo, mid) + SumRange(a, mid, hi)
  decreases mid - lo
{
  if lo == mid {
  } else {
    SumRangeSplit(a, lo + 1, mid, hi);
  }
}

lemma SumRangeExtend(a: seq<int>, lo: int, hi: int)
  requires 0 <= lo < hi <= |a|
  ensures SumRange(a, lo, hi) == SumRange(a, lo, hi - 1) + a[hi - 1]
  decreases hi - lo
{
  if lo == hi - 1 {
  } else {
    SumRangeExtend(a, lo + 1, hi);
  }
}

method FindEquilibrium(a: seq<int>) returns (idx: int)
  ensures idx == -1 ==> NoEquilibrium(a)
  ensures idx != -1 ==> IsEquilibrium(a, idx)
{
  var totalSum := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant totalSum == SumRange(a, 0, i)
    decreases |a| - i
  {
    SumRangeExtend(a, 0, i + 1);
    totalSum := totalSum + a[i];
    i := i + 1;
  }

  var leftSum := 0;
  i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant leftSum == SumRange(a, 0, i)
    invariant totalSum == SumRange(a, 0, |a|)
    invariant forall k :: 0 <= k < i ==> !IsEquilibrium(a, k)
    decreases |a| - i
  {
    SumRangeSplit(a, 0, i, |a|);
    SumRangeSplit(a, i, i + 1, |a|);
    assert SumRange(a, i, i + 1) == a[i] + SumRange(a, i + 1, i + 1) == a[i];
    var rightSum := totalSum - leftSum - a[i];
    assert rightSum == SumRange(a, i + 1, |a|);
    if leftSum == rightSum {
      return i;
    }
    SumRangeExtend(a, 0, i + 1);
    leftSum := leftSum + a[i];
    i := i + 1;
  }
  return -1;
}
