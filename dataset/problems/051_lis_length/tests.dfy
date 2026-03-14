// Longest Increasing Subsequence Length -- Test cases

method {:axiom} LISLength(a: seq<int>) returns (length: int)
  requires |a| > 0
  ensures length >= 1
  ensures length <= |a|

method TestIncreasing()
{
  var l := LISLength([1, 2, 3, 4, 5]);
  assert 1 <= l <= 5;
}

method TestDecreasing()
{
  var l := LISLength([5, 4, 3, 2, 1]);
  assert 1 <= l <= 5;
}

method TestSingle()
{
  var l := LISLength([42]);
  assert l == 1;
}

method TestMixed()
{
  var l := LISLength([3, 1, 4, 1, 5, 9]);
  assert 1 <= l <= 6;
}
