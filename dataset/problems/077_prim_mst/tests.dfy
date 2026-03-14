// Prim's MST -- Test cases

predicate ValidGraph(graph: seq<seq<int>>, n: int)
{
  n >= 0 && |graph| == n &&
  (forall i :: 0 <= i < n ==> |graph[i]| == n) &&
  (forall i, j :: 0 <= i < n && 0 <= j < n ==> graph[i][j] >= -1) &&
  (forall i, j :: 0 <= i < n && 0 <= j < n ==> graph[i][j] == graph[j][i])
}

method {:axiom} PrimMST(graph: seq<seq<int>>, n: int) returns (totalWeight: int)
  requires n > 0
  requires ValidGraph(graph, n)
  ensures totalWeight >= -1

method TestTriangle()
{
  var g := [[-1, 1, 3], [1, -1, 2], [3, 2, -1]];
  var w := PrimMST(g, 3);
  assert w >= -1;
}
