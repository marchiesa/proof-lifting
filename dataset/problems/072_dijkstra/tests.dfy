// Dijkstra -- Test cases

predicate ValidGraph(graph: seq<seq<int>>, n: int)
{
  n >= 0 &&
  |graph| == n &&
  (forall i :: 0 <= i < n ==> |graph[i]| == n) &&
  (forall i, j :: 0 <= i < n && 0 <= j < n ==> graph[i][j] >= -1)
}

predicate NonNegWeights(graph: seq<seq<int>>, n: int)
  requires ValidGraph(graph, n)
{
  forall i, j :: 0 <= i < n && 0 <= j < n && graph[i][j] != -1 ==> graph[i][j] >= 0
}

method {:axiom} Dijkstra(graph: seq<seq<int>>, n: int, src: int) returns (dist: seq<int>)
  requires n > 0
  requires 0 <= src < n
  requires ValidGraph(graph, n)
  requires NonNegWeights(graph, n)
  ensures |dist| == n
  ensures dist[src] >= 0
  ensures forall i :: 0 <= i < n ==> dist[i] >= -1
  ensures forall i :: 0 <= i < n && dist[i] != -1 ==> dist[i] >= 0

method TestSimple()
{
  var g := [[0, 1, 5], [-1, 0, 2], [-1, -1, 0]];
  var d := Dijkstra(g, 3, 0);
  assert d[0] == 0;
  assert |d| == 3;
}
