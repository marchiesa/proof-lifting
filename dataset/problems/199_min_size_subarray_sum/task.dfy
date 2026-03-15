// Minimum Size Subarray Sum
// Task: Add loop invariants so that Dafny can verify this program.

function SumRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + SumRange(a, lo + 1, hi)
}

function Min(a: int, b: int): int { if a <= b then a else b }

method MinSubarrayLen(a: seq<int>, target: int) returns (minLen: int)
  requires target > 0
  requires forall i :: 0 <= i < |a| ==> a[i] > 0
  ensures minLen >= 0
  ensures minLen == 0 || (1 <= minLen <= |a|)
{
  minLen := 0;
  var left := 0;
  var sum := 0;
  var right := 0;
  while right < |a|
  {
    sum := sum + a[right];
    right := right + 1;
    while sum >= target && left < right
    {
      var windowLen := right - left;
      if minLen == 0 || windowLen < minLen {
        minLen := windowLen;
      }
      sum := sum - a[left];
      left := left + 1;
    }
  }
}
