// Dijkstra Single Source Shortest Path (Array-Based) -- Reference solution with invariants

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
    invariant 0 <= iter <= n
    invariant |dist| == n
    invariant |visited| == n
    invariant dist[src] >= 0
    invariant forall i :: 0 <= i < n ==> dist[i] >= -1
    invariant forall i :: 0 <= i < n && dist[i] != -1 ==> dist[i] >= 0
    decreases n - iter
  {
    var u := -1;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant u == -1 || (0 <= u < n && !visited[u] && dist[u] >= 0)
      decreases n - i
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
    assert dist[u] >= 0;
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |dist| == n
      invariant forall i :: 0 <= i < n ==> dist[i] >= -1
      invariant forall i :: 0 <= i < n && dist[i] != -1 ==> dist[i] >= 0
      invariant dist[src] >= 0
      invariant dist[u] >= 0
      decreases n - j
    {
      if graph[u][j] != -1 {
        assert graph[u][j] >= 0;
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
