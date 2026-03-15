// Maximum Circular Subarray Sum (simplified) -- Reference solution with invariants

function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

function SumRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + SumRange(a, lo + 1, hi)
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

predicate IsMaxCircularSubarraySum(a: seq<int>, result: int)
  requires |a| > 0
{
  (exists lo, hi :: 0 <= lo < hi <= |a| && SumRange(a, lo, hi) == result) &&
  (forall lo, hi :: 0 <= lo < hi <= |a| ==> SumRange(a, lo, hi) <= result)
}

method MaxCircularSubarray(a: seq<int>) returns (result: int)
  requires |a| > 0
  ensures IsMaxCircularSubarraySum(a, result)
{
  result := a[0];
  var bestLo := 0;
  var bestHi := 1;
  assert SumRange(a, 0, 1) == a[0] + SumRange(a, 1, 1) == a[0];

  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant 0 <= bestLo < bestHi <= |a|
    invariant SumRange(a, bestLo, bestHi) == result
    invariant forall lo, hi :: 0 <= lo < hi <= |a| && lo < i ==> SumRange(a, lo, hi) <= result
    decreases |a| - i
  {
    var s := 0;
    var j := i;
    while j < |a|
      invariant i <= j <= |a|
      invariant s == SumRange(a, i, j)
      invariant 0 <= bestLo < bestHi <= |a|
      invariant SumRange(a, bestLo, bestHi) == result
      invariant forall lo, hi :: 0 <= lo < hi <= |a| && lo < i ==> SumRange(a, lo, hi) <= result
      invariant forall hi' :: i < hi' <= j ==> SumRange(a, i, hi') <= result
      decreases |a| - j
    {
      SumRangeExtend(a, i, j + 1);
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
