// Product of Array Except Self

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

method Main()
{
  // [1,2,3,4] => [24,12,8,6]
  var a := [1, 2, 3, 4];
  var r := ProductExceptSelf(a);
  expect |r| == 4;
  expect r[0] == ProductExceptAt(a, 0);
  expect ProductExceptAt(a, 0) == 24;
  expect r[0] == 24;
  expect r[1] == 12;
  expect r[2] == 8;
  expect r[3] == 6;

  // Single element
  var b := [5];
  var rb := ProductExceptSelf(b);
  expect |rb| == 1;
  expect rb[0] == 1;

  // With zero
  var c := [0, 1, 2];
  var rc := ProductExceptSelf(c);
  expect rc[0] == ProductExceptAt(c, 0);
  expect ProductExceptAt(c, 0) == 2;
  expect rc[0] == 2;

  print "All spec tests passed\n";
}
