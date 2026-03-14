// Dijkstra Single Source Shortest Path (Array-Based)
// Task: Add loop invariants so that Dafny can verify this program.

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

method Dijkstra(graph: seq<seq<int>>, n: int, src: int) returns (dist: seq<int>)
  requires n > 0
  requires 0 <= src < n
  requires ValidGraph(graph, n)
  requires NonNegWeights(graph, n)
  ensures |dist| == n
  ensures dist[src] >= 0
  ensures forall i :: 0 <= i < n ==> dist[i] >= -1
  ensures forall i :: 0 <= i < n && dist[i] != -1 ==> dist[i] >= 0
{
  dist := seq(n, i => if i == src then 0 else -1);
  var visited := seq(n, _ => false);
  var iter := 0;
  while iter < n
  {
    var u := -1;
    var i := 0;
    while i < n
    {
      if !visited[i] && dist[i] != -1 {
        if u == -1 || dist[i] < dist[u] {
          u := i;
        }
      }
      i := i + 1;
    }
    if u == -1 { break; }
    visited := visited[u := true];
    var j := 0;
    while j < n
    {
      if graph[u][j] != -1 {
        var newDist := dist[u] + graph[u][j];
        if dist[j] == -1 || newDist < dist[j] {
          dist := dist[j := newDist];
        }
      }
      j := j + 1;
    }
    iter := iter + 1;
  }
}
