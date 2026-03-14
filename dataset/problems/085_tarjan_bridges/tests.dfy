// Tarjan's Bridges -- Test cases

method {:axiom} FindBridges(graph: seq<seq<bool>>, n: int) returns (bridges: seq<(int,int)>)
  requires n >= 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  requires forall i, j :: 0 <= i < n && 0 <= j < n ==> graph[i][j] == graph[j][i]
  ensures forall k :: 0 <= k < |bridges| ==> 0 <= bridges[k].0 < n && 0 <= bridges[k].1 < n

method TestBridge()
{
  var g := [[false, true, false], [true, false, true], [false, true, false]];
  var b := FindBridges(g, 3);
  // 0-1 and 1-2 are both bridges
}
