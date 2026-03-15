// Subarray Sum Equals K -- Reference solution with invariants

function SumRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + SumRange(a, lo + 1, hi)
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
      sum := sum + a[j];
      if sum == k {
        count := count + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
