// BFS Shortest Path -- Test cases

method {:axiom} BFS(graph: seq<seq<bool>>, n: int, src: int) returns (dist: seq<int>)
  requires n > 0
  requires 0 <= src < n
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  ensures |dist| == n
  ensures dist[src] >= 0
  ensures forall i :: 0 <= i < n ==> dist[i] >= -1

method TestSimple()
{
  var g := [[false, true, false], [false, false, true], [false, false, false]];
  var d := BFS(g, 3, 0);
  assert d[0] >= 0;
  assert |d| == 3;
}
