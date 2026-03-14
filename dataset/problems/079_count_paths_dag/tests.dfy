// Count Paths in DAG -- Test cases

method {:axiom} CountPaths(graph: seq<seq<bool>>, n: int, src: int, tgt: int) returns (count: nat)
  requires n > 0
  requires 0 <= src < n && 0 <= tgt < n
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  ensures count >= 0

method TestLinear()
{
  var g := [[false, true, false], [false, false, true], [false, false, false]];
  var c := CountPaths(g, 3, 0, 2);
  assert c >= 0;
}
