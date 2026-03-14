// LIS -- Test cases

method {:axiom} LIS(a: seq<int>) returns (length: nat)
  ensures length <= |a|

method TestBasic()
{
  var l := LIS([3, 1, 4, 1, 5, 9, 2, 6]);
  assert l <= 8;
}

method TestSorted()
{
  var l := LIS([1, 2, 3, 4, 5]);
  assert l <= 5;
}

method TestEmpty()
{
  var l := LIS([]);
  assert l == 0;
}
