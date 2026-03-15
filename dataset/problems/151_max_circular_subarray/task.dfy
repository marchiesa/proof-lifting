// Maximum Circular Subarray Sum (simplified)
// Task: Add loop invariants so that Dafny can verify this program.

function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

function SumRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + SumRange(a, lo + 1, hi)
}

predicate IsMaxCircularSubarraySum(a: seq<int>, result: int)
  requires |a| > 0
{
  // result is achievable as some subarray sum (contiguous, possibly wrapping)
  (exists lo, hi :: 0 <= lo < hi <= |a| && SumRange(a, lo, hi) == result) &&
  // result is at least as large as any contiguous subarray
  (forall lo, hi :: 0 <= lo < hi <= |a| ==> SumRange(a, lo, hi) <= result)
}

method MaxCircularSubarray(a: seq<int>) returns (result: int)
  requires |a| > 0
  ensures IsMaxCircularSubarraySum(a, result)
{
  // Simple O(n^2): try all subarrays
  result := a[0];
  var bestLo := 0;
  var bestHi := 1;
  var i := 0;
  while i < |a|
  {
    var s := 0;
    var j := i;
    while j < |a|
    {
      s := s + a[j];
      if s > result {
        result := s;
        bestLo := i;
        bestHi := j + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
