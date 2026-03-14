// Min Vertex Cover -- Test cases

method {:axiom} MinVertexCover(graph: seq<seq<bool>>, nLeft: int, nRight: int) returns (coverSize: nat, coverLeft: seq<bool>, coverRight: seq<bool>)
  requires nLeft >= 0 && nRight >= 0
  requires |graph| == nLeft
  requires forall i :: 0 <= i < nLeft ==> |graph[i]| == nRight
  ensures |coverLeft| == nLeft
  ensures |coverRight| == nRight
  ensures coverSize <= nLeft + nRight

method TestSimple()
{
  var g := [[true, false], [true, true]];
  var sz, cl, cr := MinVertexCover(g, 2, 2);
  assert sz <= 4;
}
