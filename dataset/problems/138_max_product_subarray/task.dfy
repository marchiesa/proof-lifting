// Maximum Product Subarray
// Task: Add loop invariants so that Dafny can verify this program.
// Find the contiguous subarray with the largest product.

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
  var i := 0;
  while i < |a|
  {
    var j := i + 1;
    while j <= |a|
    {
      var p := Product(a, i, j);
      if p > maxProd {
        maxProd := p;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
