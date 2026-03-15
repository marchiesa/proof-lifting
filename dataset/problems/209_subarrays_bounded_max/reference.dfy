// Subarrays with Bounded Max -- Reference solution with invariants

method CountBoundedSubarrays(a: seq<int>, L: int, R: int) returns (count: int)
  requires 1 <= L <= R
  ensures count >= 0
{
  count := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant count >= 0
    decreases |a| - i
  {
    var maxVal := 0;
    var j := i;
    while j < |a|
      invariant i <= j <= |a|
      invariant count >= 0
      invariant j > i ==> maxVal >= a[i]
      decreases |a| - j
    {
      if j == i || a[j] > maxVal {
        maxVal := a[j];
      }
      if L <= maxVal <= R {
        count := count + 1;
      }
      if maxVal > R {
        break;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
