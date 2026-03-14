// Kth Smallest Element -- Test cases

method {:axiom} KthSmallest(a: seq<int>, k: nat) returns (result: int)
  requires |a| > 0
  requires 0 <= k < |a|
  ensures result in multiset(a)

method TestFirst()
{
  var r := KthSmallest([3, 1, 4, 1, 5], 0);
  assert r in multiset([3, 1, 4, 1, 5]);
}

method TestMiddle()
{
  var r := KthSmallest([3, 1, 4, 1, 5], 2);
  assert r in multiset([3, 1, 4, 1, 5]);
}

method TestLast()
{
  var r := KthSmallest([3, 1, 4, 1, 5], 4);
  assert r in multiset([3, 1, 4, 1, 5]);
}

method TestSingle()
{
  var r := KthSmallest([42], 0);
  assert r in multiset([42]);
}
