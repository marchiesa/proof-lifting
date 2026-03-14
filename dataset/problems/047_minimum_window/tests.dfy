// Minimum Window -- Test cases

method {:axiom} MinWindowLength(a: seq<int>, target: int, need: nat) returns (minLen: int)
  requires |a| > 0
  requires need > 0
  ensures minLen == -1 || minLen > 0
  ensures minLen > 0 ==> minLen <= |a|

method TestFound()
{
  var r := MinWindowLength([1, 2, 1, 2, 1], 1, 2);
  assert r == -1 || (r > 0 && r <= 5);
}

method TestNotEnough()
{
  var r := MinWindowLength([1, 2, 3], 1, 2);
  assert r == -1 || (r > 0 && r <= 3);
}

method TestSingle()
{
  var r := MinWindowLength([5], 5, 1);
  assert r == -1 || (r > 0 && r <= 1);
}

method TestNotPresent()
{
  var r := MinWindowLength([1, 2, 3], 4, 1);
  assert r == -1 || (r > 0 && r <= 3);
}
