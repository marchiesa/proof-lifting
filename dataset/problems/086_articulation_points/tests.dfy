// Articulation Points -- Test cases

method {:axiom} FindArticulationPoints(graph: seq<seq<bool>>, n: int) returns (isAP: seq<bool>)
  requires n >= 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  requires forall i, j :: 0 <= i < n && 0 <= j < n ==> graph[i][j] == graph[j][i]
  ensures |isAP| == n

method TestSimple()
{
  // Path graph: 0-1-2
  var g := [[false, true, false], [true, false, true], [false, true, false]];
  var ap := FindArticulationPoints(g, 3);
  assert |ap| == 3;
}
