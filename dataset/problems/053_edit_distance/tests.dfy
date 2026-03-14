// Edit Distance -- Test cases

method {:axiom} EditDistance(s: seq<int>, t: seq<int>) returns (dist: int)
  ensures dist >= 0
  ensures dist <= |s| + |t|

method TestIdentical()
{
  var d := EditDistance([1, 2, 3], [1, 2, 3]);
  assert d >= 0;
  assert d <= 6;
}

method TestEmpty()
{
  var d := EditDistance([], [1, 2, 3]);
  assert d >= 0;
  assert d <= 3;
}

method TestBothEmpty()
{
  var d := EditDistance([], []);
  assert d >= 0;
  assert d <= 0;
  assert d == 0;
}

method TestSingle()
{
  var d := EditDistance([1], [2]);
  assert d >= 0;
  assert d <= 2;
}
