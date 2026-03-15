// Dot Product
// Task: Add loop invariants so that Dafny can verify this program.
// Compute the dot product of two sequences of equal length.

function DotProd(a: seq<int>, b: seq<int>): int
  requires |a| == |b|
  decreases |a|
{
  if |a| == 0 then 0
  else a[0] * b[0] + DotProd(a[1..], b[1..])
}

method ComputeDotProduct(a: seq<int>, b: seq<int>) returns (result: int)
  requires |a| == |b|
  ensures result == DotProd(a, b)
{
  result := 0;
  var i := 0;
  while i < |a|
  {
    result := result + a[i] * b[i];
    i := i + 1;
  }
}
