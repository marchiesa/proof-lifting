// Kth Smallest Element -- Test cases

method {:axiom} KthSmallest(a: seq<int>, k: int) returns (result: int)
  requires |a| > 0
  requires 1 <= k <= |a|
  ensures result in multiset(a)

method TestBasic()
{
  var a := [3, 1, 4, 1, 5];
  var r := KthSmallest(a, 1);
  assert r in multiset(a);
}

method TestSecond()
{
  var a := [3, 1, 4, 1, 5];
  var r := KthSmallest(a, 2);
  assert r in multiset(a);
}

method TestLast()
{
  var a := [3, 1, 4, 1, 5];
  var r := KthSmallest(a, 5);
  assert r in multiset(a);
}

method TestSingle()
{
  var a := [7];
  var r := KthSmallest(a, 1);
  assert r in multiset(a);
  // a only has 7, so result must be 7
  assert r == 7;
}
