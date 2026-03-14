// Bellman-Ford Shortest Paths -- Test cases

function Inf(): int { 1000000 }

method {:axiom} BellmanFord(n: int, edges: seq<(int, int, int)>, source: int) returns (dist: array<int>)
  requires n > 0
  requires 0 <= source < n
  requires forall e :: e in edges ==> 0 <= e.0 < n && 0 <= e.1 < n
  requires forall e :: e in edges ==> e.2 >= 0
  ensures dist.Length == n
  ensures dist[source] == 0
  ensures forall v :: 0 <= v < n ==> dist[v] <= Inf()

method TestSingleNode()
{
  var d := BellmanFord(1, [], 0);
  assert d[0] == 0;
}

method TestNoEdges()
{
  var d := BellmanFord(3, [], 0);
  assert d[0] == 0;
  assert d[1] <= Inf();
  assert d[2] <= Inf();
}

method TestSimpleEdge()
{
  var d := BellmanFord(2, [(0, 1, 5)], 0);
  assert d[0] == 0;
  assert d[1] <= Inf();
}
