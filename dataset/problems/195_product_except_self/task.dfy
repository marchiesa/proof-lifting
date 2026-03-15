// Product of Array Except Self
// Task: Add loop invariants so that Dafny can verify this program.

function Product(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 1
  else a[lo] * Product(a, lo + 1, hi)
}

function ProductExceptAt(a: seq<int>, idx: int): int
  requires 0 <= idx < |a|
{
  Product(a, 0, idx) * Product(a, idx + 1, |a|)
}

method ProductExceptSelf(a: seq<int>) returns (result: seq<int>)
  requires |a| > 0
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> result[i] == ProductExceptAt(a, i)
{
  // Build prefix products
  var prefix := [1];
  var i := 0;
  while i < |a|
  {
    prefix := prefix + [prefix[i] * a[i]];
    i := i + 1;
  }

  // Build suffix products and combine
  result := [];
  var suffix := 1;
  i := |a| - 1;
  while i >= 0
  {
    result := [prefix[i] * suffix] + result;
    suffix := suffix * a[i];
    i := i - 1;
  }
}
