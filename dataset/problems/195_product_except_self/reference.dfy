// Product of Array Except Self -- Reference solution with invariants

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
    invariant 0 <= i <= |a|
    invariant |prefix| == i + 1
    invariant forall k :: 0 <= k <= i ==> prefix[k] == Product(a, 0, k)
    decreases |a| - i
  {
    prefix := prefix + [prefix[i] * a[i]];
    i := i + 1;
  }

  // Build result from right to left
  result := seq(|a|, k => 0);
  var suffix := 1;
  i := |a| - 1;
  while i >= 0
    invariant -1 <= i <= |a| - 1
    invariant |result| == |a|
    invariant suffix == Product(a, i + 1, |a|)
    invariant forall k :: i + 1 <= k < |a| ==> result[k] == ProductExceptAt(a, k)
    decreases i + 1
  {
    result := result[..i] + [prefix[i] * suffix] + result[i+1..];
    suffix := suffix * a[i];
    i := i - 1;
  }
}
