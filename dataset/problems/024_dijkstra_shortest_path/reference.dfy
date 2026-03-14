// Dijkstra's Shortest Path (Simplified) -- Reference solution with invariants

// Find the unvisited node with minimum distance
method FindMinDist(dist: seq<int>, visited: seq<bool>, n: int) returns (minNode: int)
  requires |dist| == n && |visited| == n && n > 0
  ensures -1 <= minNode < n
  ensures minNode >= 0 ==> !visited[minNode] && dist[minNode] >= 0
  ensures minNode >= 0 ==> (forall k :: 0 <= k < n && !visited[k] && dist[k] >= 0 ==> dist[minNode] <= dist[k])
  ensures minNode == -1 ==> forall k :: 0 <= k < n ==> visited[k] || dist[k] < 0
{
  minNode := -1;
  var minDist := -1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant -1 <= minNode < n
    invariant minNode >= 0 ==> !visited[minNode] && dist[minNode] >= 0
    invariant minNode >= 0 ==> minDist == dist[minNode]
    invariant minNode >= 0 ==> (forall k :: 0 <= k < i && !visited[k] && dist[k] >= 0 ==> dist[minNode] <= dist[k])
    invariant minNode == -1 ==> forall k :: 0 <= k < i ==> visited[k] || dist[k] < 0
    decreases n - i
  {
    if !visited[i] && dist[i] >= 0 && (minNode == -1 || dist[i] < minDist) {
      minNode := i;
      minDist := dist[i];
    }
    i := i + 1;
  }
}

method Dijkstra(graph: seq<seq<int>>, n: int, src: int) returns (dist: seq<int>)
  requires n > 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  requires 0 <= src < n
  requires forall i, j :: 0 <= i < n && 0 <= j < n ==> graph[i][j] >= -1
  requires forall i :: 0 <= i < n ==> graph[i][i] == 0 || graph[i][i] == -1
  ensures |dist| == n
  ensures dist[src] == 0
  ensures forall i :: 0 <= i < n ==> dist[i] >= -1
{
  dist := seq(n, i => if i == src then 0 else -1);
  var visited := seq(n, _ => false);

  var round := 0;
  while round < n
    invariant 0 <= round <= n
    invariant |dist| == n
    invariant |visited| == n
    invariant dist[src] == 0
    invariant forall i :: 0 <= i < n ==> dist[i] >= -1
    decreases n - round
  {
    var u := FindMinDist(dist, visited, n);
    if u == -1 {
      break;
    }
    visited := visited[u := true];

    var v := 0;
    while v < n
      invariant 0 <= v <= n
      invariant |dist| == n
      invariant |visited| == n
      invariant dist[src] == 0
      invariant forall i :: 0 <= i < n ==> dist[i] >= -1
      decreases n - v
    {
      if graph[u][v] > 0 && !visited[v] {
        var newDist := dist[u] + graph[u][v];
        if dist[v] == -1 || newDist < dist[v] {
          // Key: v != src because if v == src, dist[src] == 0
          // and newDist >= dist[u] + 1 >= 1 > 0 == dist[src],
          // so newDist < dist[v] would be false
          assert v == src ==> dist[v] == 0;
          assert v == src ==> newDist >= 1;
          assert v == src ==> !(newDist < dist[v]);
          assert v != src;
          dist := dist[v := newDist];
        }
      }
      v := v + 1;
    }
    round := round + 1;
  }
}
