// Pattern: Compute dot product of two vectors
// Source: various numerical/scientific computing libraries
// Real-world: ML inference, signal processing, physics simulations

ghost function DotProduct(a: seq<int>, b: seq<int>): int
  requires |a| == |b|
{
  if |a| == 0 then 0
  else DotProduct(a[..|a|-1], b[..|b|-1]) + a[|a|-1] * b[|b|-1]
}

method ComputeDotProduct(a: seq<int>, b: seq<int>) returns (result: int)
  requires |a| == |b|
  ensures result == DotProduct(a, b)
{
  result := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant result == DotProduct(a[..i], b[..i])
  {
    assert a[..i+1] == a[..i] + [a[i]];  // SMT QUIRK: B1 sequence extensionality
    assert b[..i+1] == b[..i] + [b[i]];  // SMT QUIRK: B1 sequence extensionality (both seqs)
    result := result + a[i] * b[i];
    i := i + 1;
  }
  assert a[..|a|] == a;  // SMT QUIRK: B1 take-full
  assert b[..|b|] == b;  // SMT QUIRK: B1 take-full
}
