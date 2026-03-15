// Subarray Sum Equals K -- Reference solution with invariants

function SumRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + SumRange(a, lo + 1, hi)
}

lemma SumRangeExtend(a: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi < |a|
  ensures SumRange(a, lo, hi + 1) == SumRange(a, lo, hi) + a[hi]
  decreases hi - lo
{
  if lo == hi {
    // SumRange(a, lo, lo+1) == a[lo] + SumRange(a, lo+1, lo+1) == a[lo] + 0 == a[lo]
    // SumRange(a, lo, lo) + a[lo] == 0 + a[lo] == a[lo]
  } else {
    // SumRange(a, lo, hi+1) == a[lo] + SumRange(a, lo+1, hi+1)
    SumRangeExtend(a, lo + 1, hi);
    // SumRange(a, lo+1, hi+1) == SumRange(a, lo+1, hi) + a[hi]
    // So SumRange(a, lo, hi+1) == a[lo] + SumRange(a, lo+1, hi) + a[hi]
    //                           == SumRange(a, lo, hi) + a[hi]
  }
}

method SubarraySumK(a: seq<int>, k: int) returns (count: int)
  ensures count >= 0
{
  count := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant count >= 0
    decreases |a| - i
  {
    var sum := 0;
    var j := i;
    while j < |a|
      invariant i <= j <= |a|
      invariant sum == SumRange(a, i, j)
      invariant count >= 0
      decreases |a| - j
    {
      SumRangeExtend(a, i, j);
      sum := sum + a[j];
      if sum == k {
        count := count + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
