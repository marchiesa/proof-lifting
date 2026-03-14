// LCS -- Test cases

function LCSLen(a: seq<int>, b: seq<int>): nat
  decreases |a|, |b|
{
  if |a| == 0 || |b| == 0 then 0
  else if a[|a|-1] == b[|b|-1] then 1 + LCSLen(a[..|a|-1], b[..|b|-1])
  else if LCSLen(a[..|a|-1], b) >= LCSLen(a, b[..|b|-1]) then LCSLen(a[..|a|-1], b) else LCSLen(a, b[..|b|-1])
}

method {:axiom} ComputeLCS(a: seq<int>, b: seq<int>) returns (result: nat)
  ensures result == LCSLen(a, b)

method TestIdentical()
{
  var r := ComputeLCS([1, 2, 3], [1, 2, 3]);
  assert LCSLen([1, 2, 3], [1, 2, 3]) == 3;
  assert r == 3;
}

method TestEmpty()
{
  var r := ComputeLCS([], [1, 2]);
  assert r == 0;
}
