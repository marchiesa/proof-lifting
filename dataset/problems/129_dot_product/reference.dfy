// Dot Product -- Reference solution with invariants

function DotProd(a: seq<int>, b: seq<int>): int
  requires |a| == |b|
  decreases |a|
{
  if |a| == 0 then 0
  else a[0] * b[0] + DotProd(a[1..], b[1..])
}

lemma DotProdSplit(a: seq<int>, b: seq<int>, i: int)
  requires |a| == |b|
  requires 0 <= i < |a|
  ensures DotProd(a[..i+1], b[..i+1]) == DotProd(a[..i], b[..i]) + a[i] * b[i]
{
  if i == 0 {
    assert a[..1] == [a[0]];
    assert b[..1] == [b[0]];
    assert a[..0] == [];
    assert b[..0] == [];
  } else {
    assert a[..i+1] == [a[0]] + a[1..i+1];
    assert b[..i+1] == [b[0]] + b[1..i+1];
    assert a[..i] == [a[0]] + a[1..i];
    assert b[..i] == [b[0]] + b[1..i];
    assert (a[..i+1])[1..] == a[1..i+1];
    assert (b[..i+1])[1..] == b[1..i+1];
    assert (a[..i])[1..] == a[1..i];
    assert (b[..i])[1..] == b[1..i];
    DotProdSplit(a[1..], b[1..], i - 1);
    assert a[1..][..i] == a[1..i+1];
    assert b[1..][..i] == b[1..i+1];
    assert a[1..][..i-1] == a[1..i];
    assert b[1..][..i-1] == b[1..i];
    assert a[1..][i-1] == a[i];
    assert b[1..][i-1] == b[i];
  }
}

method ComputeDotProduct(a: seq<int>, b: seq<int>) returns (result: int)
  requires |a| == |b|
  ensures result == DotProd(a, b)
{
  result := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant result == DotProd(a[..i], b[..i])
    decreases |a| - i
  {
    DotProdSplit(a, b, i);
    result := result + a[i] * b[i];
    i := i + 1;
  }
  assert a[..i] == a;
  assert b[..i] == b;
}
