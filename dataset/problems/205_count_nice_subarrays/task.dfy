// Count Nice Subarrays
// Task: Add loop invariants so that Dafny can verify this program.

function CountOdds(a: seq<int>, lo: int, hi: int): nat
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else (if a[lo] % 2 != 0 then 1 else 0) + CountOdds(a, lo + 1, hi)
}

method CountNiceSubarrays(a: seq<int>, k: int) returns (count: int)
  requires k >= 1
  ensures count >= 0
{
  count := 0;
  var i := 0;
  while i < |a|
  {
    var odds := 0;
    var j := i;
    while j < |a|
    {
      if a[j] % 2 != 0 {
        odds := odds + 1;
      }
      if odds == k {
        count := count + 1;
      }
      if odds > k {
        break;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
