// Edmonds-Karp -- Test cases

method {:axiom} EdmondsKarp(cap: array2<int>, n: int, src: int, sink: int) returns (maxFlow: int)
  requires n > 0
  requires 0 <= src < n && 0 <= sink < n && src != sink
  requires cap.Length0 == n && cap.Length1 == n
  requires forall i, j :: 0 <= i < n && 0 <= j < n ==> cap[i, j] >= 0
  modifies cap
  ensures maxFlow >= 0

method TestSimple()
{
  var cap := new int[2, 2]((i, j) => if i == 0 && j == 1 then 10 else 0);
  var f := EdmondsKarp(cap, 2, 0, 1);
  assert f >= 0;
}
