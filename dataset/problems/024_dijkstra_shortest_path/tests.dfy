// Dijkstra's Shortest Path -- Test cases

method {:axiom} Dijkstra(graph: seq<seq<int>>, n: int, src: int) returns (dist: seq<int>)
  requires n > 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  requires 0 <= src < n
  requires forall i, j :: 0 <= i < n && 0 <= j < n ==> graph[i][j] >= -1
  requires forall i :: 0 <= i < n ==> graph[i][i] == 0 || graph[i][i] == -1
  ensures |dist| == n
  ensures dist[src] == 0
  ensures forall i :: 0 <= i < n ==> dist[i] >= -1

method TestSimple()
{
  var graph := [[0, 4, -1], [-1, 0, 1], [-1, -1, 0]];
  var dist := Dijkstra(graph, 3, 0);
  assert |dist| == 3;
  assert dist[0] == 0;
  assert dist[1] >= -1;
  assert dist[2] >= -1;
}

method TestSingleNode()
{
  var graph := [[0]];
  var dist := Dijkstra(graph, 1, 0);
  assert |dist| == 1;
  assert dist[0] == 0;
}

method TestDisconnected()
{
  var graph := [[0, -1], [-1, 0]];
  var dist := Dijkstra(graph, 2, 0);
  assert |dist| == 2;
  assert dist[0] == 0;
  assert dist[1] >= -1;
}

method TestChain()
{
  var graph := [[0, 1, -1], [-1, 0, 2], [-1, -1, 0]];
  var dist := Dijkstra(graph, 3, 0);
  assert |dist| == 3;
  assert dist[0] == 0;
}
