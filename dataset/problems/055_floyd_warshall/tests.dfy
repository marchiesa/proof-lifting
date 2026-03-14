// Floyd-Warshall All-Pairs Shortest Paths -- Test cases

function Inf(): int { 1000000 }

method {:axiom} FloydWarshall(n: int, edges: seq<(int, int, int)>) returns (dist: array2<int>)
  requires n > 0
  requires forall e :: e in edges ==> 0 <= e.0 < n && 0 <= e.1 < n && e.2 >= 0
  ensures dist.Length0 == n && dist.Length1 == n
  ensures forall i :: 0 <= i < n ==> dist[i, i] == 0
  ensures forall i, j :: 0 <= i < n && 0 <= j < n ==> dist[i, j] <= Inf()

method TestSingleNode()
{
  var d := FloydWarshall(1, []);
  assert d[0, 0] == 0;
}

method TestNoEdges()
{
  var d := FloydWarshall(3, []);
  assert d[0, 0] == 0;
  assert d[1, 1] == 0;
  assert d[2, 2] == 0;
  assert d[0, 1] <= Inf();
}

method TestSimpleEdge()
{
  var d := FloydWarshall(2, [(0, 1, 3)]);
  assert d[0, 0] == 0;
  assert d[1, 1] == 0;
  assert d[0, 1] <= Inf();
}
