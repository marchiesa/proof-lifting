// Maximum Product Subarray -- Reference solution with invariants

function Product(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 1
  else a[lo] * Product(a, lo + 1, hi)
}

predicate IsMaxProduct(a: seq<int>, maxProd: int)
  requires |a| > 0
{
  (exists lo, hi :: 0 <= lo < hi <= |a| && Product(a, lo, hi) == maxProd) &&
  (forall lo, hi :: 0 <= lo < hi <= |a| ==> Product(a, lo, hi) <= maxProd)
}

method MaxProductSubarray(a: seq<int>) returns (maxProd: int)
  requires |a| > 0
  ensures IsMaxProduct(a, maxProd)
{
  maxProd := a[0];
  ghost var bestLo := 0;
  ghost var bestHi := 1;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant 0 <= bestLo < bestHi <= |a|
    invariant Product(a, bestLo, bestHi) == maxProd
    invariant forall lo, hi :: 0 <= lo && lo < i && lo < hi && hi <= |a| ==> Product(a, lo, hi) <= maxProd
    decreases |a| - i
  {
    var j := i + 1;
    while j <= |a|
      invariant i + 1 <= j <= |a| + 1
      invariant 0 <= bestLo < bestHi <= |a|
      invariant Product(a, bestLo, bestHi) == maxProd
      invariant forall lo, hi :: 0 <= lo && lo < i && lo < hi && hi <= |a| ==> Product(a, lo, hi) <= maxProd
      invariant forall hi' :: i < hi' && hi' < j ==> Product(a, i, hi') <= maxProd
      decreases |a| + 1 - j
    {
      var p := Product(a, i, j);
      if p > maxProd {
        maxProd := p;
        bestLo := i;
        bestHi := j;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
