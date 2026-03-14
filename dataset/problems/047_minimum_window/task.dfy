// Minimum Window Containing All Target Elements
// Task: Add loop invariants so that Dafny can verify this program.
// Find the length of the smallest contiguous subarray containing
// all elements from a target multiset.

function CountInRange(a: seq<int>, val: int, lo: int, hi: int): nat
  requires 0 <= lo <= hi <= |a|
{
  if lo == hi then 0
  else (if a[lo] == val then 1 else 0) + CountInRange(a, val, lo + 1, hi)
}

// Check if window [lo..hi) contains at least `need` copies of `val`
predicate ContainsEnough(a: seq<int>, val: int, lo: int, hi: int, need: nat)
  requires 0 <= lo <= hi <= |a|
{
  CountInRange(a, val, lo, hi) >= need
}

method MinWindowLength(a: seq<int>, target: int, need: nat) returns (minLen: int)
  requires |a| > 0
  requires need > 0
  ensures minLen == -1 || minLen > 0
  ensures minLen > 0 ==> minLen <= |a|
{
  minLen := -1;
  var left := 0;
  var right := 0;
  var count := 0;

  while right < |a|
  {
    if a[right] == target {
      count := count + 1;
    }
    right := right + 1;

    while count >= need && left < right
    {
      var windowLen := right - left;
      if minLen == -1 || windowLen < minLen {
        minLen := windowLen;
      }
      if a[left] == target {
        count := count - 1;
      }
      left := left + 1;
    }
  }
}
