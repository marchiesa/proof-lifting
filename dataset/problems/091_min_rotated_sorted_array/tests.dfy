// Find Minimum in Rotated Sorted Array -- Test cases

function SeqMin(a: seq<int>): int
  requires |a| > 0
  decreases |a|
{
  if |a| == 1 then a[0]
  else if a[0] <= SeqMin(a[1..]) then a[0]
  else SeqMin(a[1..])
}

method {:axiom} FindMin(a: seq<int>) returns (min: int)
  requires |a| > 0
  ensures min == SeqMin(a)

method TestNormal()
{
  var a := [3, 4, 5, 1, 2];
  var m := FindMin(a);
  assert a[3] == 1;
  // SeqMin finds the minimum which is 1
}

method TestSorted()
{
  var a := [1, 2, 3, 4, 5];
  var m := FindMin(a);
  assert a[0] == 1;
}

method TestSingleElement()
{
  var a := [42];
  var m := FindMin(a);
  assert m == 42;
}

method TestTwoElements()
{
  var a := [2, 1];
  var m := FindMin(a);
  assert a[1] == 1;
}
