// Edit Distance -- Test cases

method {:axiom} EditDistance(a: seq<int>, b: seq<int>) returns (dist: int)
  ensures dist >= 0
  ensures dist <= |a| + |b|

method TestDeletion()
{
  var a := [1, 2, 3];
  var b := [1, 3];
  var d := EditDistance(a, b);
  assert d >= 0;
  assert d <= 5;
}

method TestIdentical()
{
  var a := [1, 2, 3];
  var b := [1, 2, 3];
  var d := EditDistance(a, b);
  assert d >= 0;
  assert d <= 6;
}

method TestEmpty()
{
  var a: seq<int> := [];
  var b := [1, 2];
  var d := EditDistance(a, b);
  assert d >= 0;
  assert d <= 2;
}

method TestBothEmpty()
{
  var a: seq<int> := [];
  var b: seq<int> := [];
  var d := EditDistance(a, b);
  assert d >= 0;
  assert d <= 0;
  assert d == 0;
}
