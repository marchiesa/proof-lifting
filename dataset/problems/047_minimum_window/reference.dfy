// Minimum Window Containing All Target Elements -- Reference solution with invariants

function CountInRange(a: seq<int>, val: int, lo: int, hi: int): nat
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else (if a[lo] == val then 1 else 0) + CountInRange(a, val, lo + 1, hi)
}

lemma CountInRangeStep(a: seq<int>, val: int, lo: int, hi: int)
  requires 0 <= lo < hi <= |a|
  ensures CountInRange(a, val, lo, hi) ==
          CountInRange(a, val, lo, hi - 1) + (if a[hi - 1] == val then 1 else 0)
  decreases hi - lo
{
  if lo == hi - 1 {
  } else {
    CountInRangeStep(a, val, lo + 1, hi);
  }
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
  var count: nat := 0;

  while right < |a|
    invariant 0 <= left <= right <= |a|
    invariant count == CountInRange(a, target, left, right)
    invariant minLen == -1 || (minLen > 0 && minLen <= |a|)
    decreases |a| - right
  {
    CountInRangeStep(a, target, left, right + 1);
    if a[right] == target {
      count := count + 1;
    }
    right := right + 1;

    while count >= need && left < right
      invariant 0 <= left <= right
      invariant count == CountInRange(a, target, left, right)
      invariant minLen == -1 || (minLen > 0 && minLen <= |a|)
      decreases right - left
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
