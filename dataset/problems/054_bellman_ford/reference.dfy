// Bellman-Ford Shortest Paths -- Reference solution with invariants

function Inf(): int { 1000000 }

method BellmanFord(n: int, edges: seq<(int, int, int)>, source: int) returns (dist: array<int>)
  requires n > 0
  requires 0 <= source < n
  requires forall e :: e in edges ==> 0 <= e.0 < n && 0 <= e.1 < n
  requires forall e :: e in edges ==> e.2 >= 0  // non-negative weights
  ensures dist.Length == n
  ensures dist[source] == 0
  ensures forall v :: 0 <= v < n ==> dist[v] <= Inf()
{
  dist := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> dist[k] == Inf()
    decreases n - i
  {
    dist[i] := Inf();
    i := i + 1;
  }
  dist[source] := 0;

  var iter := 0;
  while iter < n - 1
    invariant 0 <= iter <= n - 1
    invariant dist.Length == n
    invariant dist[source] == 0
    invariant forall v :: 0 <= v < n ==> dist[v] >= 0
    invariant forall v :: 0 <= v < n ==> dist[v] <= Inf()
    decreases n - 1 - iter
  {
    var j := 0;
    while j < |edges|
      invariant 0 <= j <= |edges|
      invariant dist.Length == n
      invariant dist[source] == 0
      invariant forall v :: 0 <= v < n ==> dist[v] >= 0
      invariant forall v :: 0 <= v < n ==> dist[v] <= Inf()
      decreases |edges| - j
    {
      var u := edges[j].0;
      var v := edges[j].1;
      var w := edges[j].2;
      if dist[u] < Inf() && dist[u] + w < dist[v] {
        dist[v] := dist[u] + w;
      }
      j := j + 1;
    }
    iter := iter + 1;
  }
}
