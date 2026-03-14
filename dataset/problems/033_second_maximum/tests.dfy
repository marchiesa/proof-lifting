// Find Second Maximum -- Test cases

predicate IsMax(val: int, s: seq<int>)
{
  forall i :: 0 <= i < |s| ==> s[i] <= val
}

predicate ExistsIn(val: int, s: seq<int>)
{
  exists i :: 0 <= i < |s| && s[i] == val
}

method {:axiom} SecondMax(a: seq<int>) returns (first: int, second: int)
  requires |a| >= 2
  ensures ExistsIn(first, a)
  ensures IsMax(first, a)
  ensures ExistsIn(second, a)
  ensures second <= first
  ensures forall i :: 0 <= i < |a| && a[i] != first ==> a[i] <= second

method TestDistinct()
{
  var f, s := SecondMax([3, 1, 4, 1, 5, 9, 2, 6]);
  assert IsMax(f, [3, 1, 4, 1, 5, 9, 2, 6]);
}

method TestTwoElements()
{
  var f, s := SecondMax([10, 20]);
  assert f >= 20 || f >= 10;
  assert s <= f;
}

method TestAllEqual()
{
  var f, s := SecondMax([5, 5, 5]);
  assert f == 5;
  assert s == 5;
}
