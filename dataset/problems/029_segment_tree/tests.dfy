// Prefix Minimum Query -- Test cases

function SeqMin(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else
    var rest := SeqMin(s[1..]);
    if s[0] < rest then s[0] else rest
}

method {:axiom} BuildPrefixMin(a: seq<int>) returns (prefixMin: seq<int>)
  requires |a| > 0
  ensures |prefixMin| == |a|
  ensures prefixMin[0] == a[0]
  ensures forall i :: 0 <= i < |a| ==> prefixMin[i] == SeqMin(a[..i + 1])

method TestDecreasing()
{
  var a := [5, 4, 3, 2, 1];
  var pm := BuildPrefixMin(a);
  assert |pm| == 5;
  assert pm[0] == 5;
}

method TestIncreasing()
{
  var a := [1, 2, 3, 4, 5];
  var pm := BuildPrefixMin(a);
  assert |pm| == 5;
  assert pm[0] == 1;
  // SeqMin(a[..1]) = SeqMin([1]) = 1
  assert a[..1] == [1];
  assert pm[0] == SeqMin([1]);
}

method TestSingle()
{
  var a := [42];
  var pm := BuildPrefixMin(a);
  assert |pm| == 1;
  assert pm[0] == 42;
}

method TestWithDip()
{
  var a := [3, 1, 4, 1, 5];
  var pm := BuildPrefixMin(a);
  assert |pm| == 5;
  assert pm[0] == 3;
}
