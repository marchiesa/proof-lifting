// Floyd-Warshall All-Pairs Shortest Paths
// Task: Add loop invariants so that Dafny can verify this program.

function Inf(): int { 1000000 }

method FloydWarshall(n: int, edges: seq<(int, int, int)>) returns (dist: array2<int>)
  requires n > 0
  requires forall e :: e in edges ==> 0 <= e.0 < n && 0 <= e.1 < n && e.2 >= 0
  ensures dist.Length0 == n && dist.Length1 == n
  ensures forall i :: 0 <= i < n ==> dist[i, i] == 0
  ensures forall i, j :: 0 <= i < n && 0 <= j < n ==> dist[i, j] <= Inf()
{
  dist := new int[n, n];

  // Initialize
  var i := 0;
  while i < n
  {
    var j := 0;
    while j < n
    {
      if i == j {
        dist[i, j] := 0;
      } else {
        dist[i, j] := Inf();
      }
      j := j + 1;
    }
    i := i + 1;
  }

  // Add edges
  var e := 0;
  while e < |edges|
  {
    var u := edges[e].0;
    var v := edges[e].1;
    var w := edges[e].2;
    if w < dist[u, v] {
      dist[u, v] := w;
    }
    e := e + 1;
  }

  // Floyd-Warshall
  var k := 0;
  while k < n
  {
    i := 0;
    while i < n
    {
      var j := 0;
      while j < n
      {
        if dist[i, k] < Inf() && dist[k, j] < Inf() {
          var through_k := dist[i, k] + dist[k, j];
          if through_k < dist[i, j] {
            dist[i, j] := through_k;
          }
        }
        j := j + 1;
      }
      i := i + 1;
    }
    k := k + 1;
  }
}
