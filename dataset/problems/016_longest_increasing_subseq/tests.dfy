// Longest Increasing Subsequence Length -- Test cases

method {:axiom} LISLength(a: seq<int>) returns (length: int)
  requires |a| > 0
  ensures length >= 1
  ensures length <= |a|

method TestBasic()
{
  var a := [10, 9, 2, 5, 3, 7, 101, 18];
  var l := LISLength(a);
  assert l >= 1;
  assert l <= 8;
}

method TestIncreasing()
{
  var a := [1, 2, 3];
  var l := LISLength(a);
  assert l >= 1;
  assert l <= 3;
}

method TestDecreasing()
{
  var a := [3, 2, 1];
  var l := LISLength(a);
  assert l >= 1;
  assert l <= 3;
}

method TestSingle()
{
  var a := [5];
  var l := LISLength(a);
  assert l >= 1;
  assert l <= 1;
  assert l == 1;
}
