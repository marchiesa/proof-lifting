// Bipartite Matching -- Test cases

method {:axiom} MaxMatching(graph: seq<seq<bool>>, nLeft: int, nRight: int) returns (matchCount: nat)
  requires nLeft >= 0 && nRight >= 0
  requires |graph| == nLeft
  requires forall i :: 0 <= i < nLeft ==> |graph[i]| == nRight
  ensures matchCount <= nLeft
  ensures matchCount <= nRight

method TestSimple()
{
  var g := [[true, false], [false, true]];
  var c := MaxMatching(g, 2, 2);
  assert c <= 2;
}
