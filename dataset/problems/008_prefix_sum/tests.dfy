// Prefix Sum -- Test cases

function Sum(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + Sum(a, lo + 1, hi)
}

method {:axiom} PrefixSum(a: seq<int>) returns (p: seq<int>)
  ensures |p| == |a|
  ensures forall i :: 0 <= i < |p| ==> p[i] == Sum(a, 0, i + 1)

method TestBasic()
{
  var a := [1, 2, 3, 4];
  var p := PrefixSum(a);
  assert |p| == 4;
  assert p[0] == Sum(a, 0, 1);
  assert p[3] == Sum(a, 0, 4);
}

method TestSingle()
{
  var a := [5];
  var p := PrefixSum(a);
  assert |p| == 1;
  assert p[0] == Sum(a, 0, 1);
}

method TestEmpty()
{
  var a: seq<int> := [];
  var p := PrefixSum(a);
  assert |p| == 0;
}

method TestNegatives()
{
  var a := [-1, 1, -1, 1];
  var p := PrefixSum(a);
  assert |p| == 4;
}

method TestTwoElements()
{
  var a := [10, 20];
  var p := PrefixSum(a);
  assert |p| == 2;
  assert p[0] == Sum(a, 0, 1);
  assert p[1] == Sum(a, 0, 2);
}
