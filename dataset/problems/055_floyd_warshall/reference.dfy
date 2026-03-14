// Floyd-Warshall All-Pairs Shortest Paths -- Reference solution with invariants

function Inf(): int { 1000000 }

method FloydWarshall(n: int, edges: seq<(int, int, int)>) returns (dist: array2<int>)
  requires n > 0
  requires forall e :: e in edges ==> 0 <= e.0 < n && 0 <= e.1 < n && e.2 >= 0
  ensures dist.Length0 == n && dist.Length1 == n
  ensures forall i :: 0 <= i < n ==> dist[i, i] == 0
  ensures forall i, j :: 0 <= i < n && 0 <= j < n ==> dist[i, j] <= Inf()
{
  dist := new int[n, n];

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall a, b :: 0 <= a < i && 0 <= b < n ==>
                (if a == b then dist[a, b] == 0 else dist[a, b] == Inf())
    decreases n - i
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant forall a, b :: 0 <= a < i && 0 <= b < n ==>
                  (if a == b then dist[a, b] == 0 else dist[a, b] == Inf())
      invariant forall b :: 0 <= b < j ==>
                  (if i == b then dist[i, b] == 0 else dist[i, b] == Inf())
      decreases n - j
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

  var e := 0;
  while e < |edges|
    invariant 0 <= e <= |edges|
    invariant forall a :: 0 <= a < n ==> dist[a, a] == 0
    invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> dist[a, b] >= 0
    invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> dist[a, b] <= Inf()
    decreases |edges| - e
  {
    var u := edges[e].0;
    var v := edges[e].1;
    var w := edges[e].2;
    if w < dist[u, v] {
      dist[u, v] := w;
    }
    e := e + 1;
  }

  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant forall a :: 0 <= a < n ==> dist[a, a] == 0
    invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> dist[a, b] >= 0
    invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> dist[a, b] <= Inf()
    decreases n - k
  {
    i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant forall a :: 0 <= a < n ==> dist[a, a] == 0
      invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> dist[a, b] >= 0
      invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> dist[a, b] <= Inf()
      decreases n - i
    {
      var j := 0;
      while j < n
        invariant 0 <= j <= n
        invariant forall a :: 0 <= a < n ==> dist[a, a] == 0
        invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> dist[a, b] >= 0
        invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> dist[a, b] <= Inf()
        decreases n - j
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
