// Segment Tree -- Test cases

method {:axiom} BuildTree(a: seq<int>) returns (tree: array<int>, n: int)
  requires |a| > 0
  ensures n == |a|
  ensures tree.Length == 4 * n

method TestBuild()
{
  var tree, n := BuildTree([1, 2, 3, 4]);
  assert n == 4;
  assert tree.Length == 16;
}
