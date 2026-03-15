// Number of Subarrays with Bounded Maximum
// Task: Add loop invariants so that Dafny can verify this program.

function MaxInRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo < hi <= |a|
  decreases hi - lo
{
  if hi - lo == 1 then a[lo]
  else if a[lo] >= MaxInRange(a, lo + 1, hi) then a[lo]
  else MaxInRange(a, lo + 1, hi)
}

method CountBoundedSubarrays(a: seq<int>, L: int, R: int) returns (count: int)
  requires 1 <= L <= R
  ensures count >= 0
{
  count := 0;
  var i := 0;
  while i < |a|
  {
    var j := i + 1;
    while j <= |a|
    {
      var maxVal := a[i];
      var k := i + 1;
      while k < j
      {
        if a[k] > maxVal {
          maxVal := a[k];
        }
        k := k + 1;
      }
      if L <= maxVal <= R {
        count := count + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
