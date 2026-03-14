// Min Vertex Cover -- Runtime spec tests

// The spec:
//   ensures |coverLeft| == nLeft
//   ensures |coverRight| == nRight
//   ensures coverSize <= nLeft + nRight
// We test these spec predicates and the cover validity checker.

method CheckCoverSpec(coverLeft: seq<bool>, coverRight: seq<bool>, coverSize: nat,
                       nLeft: int, nRight: int) returns (ok: bool)
{
  ok := |coverLeft| == nLeft && |coverRight| == nRight && coverSize <= nLeft + nRight;
}

// Check that cover actually covers all edges
method CheckCoverValid(graph: seq<seq<bool>>, nLeft: int, nRight: int,
                        coverLeft: seq<bool>, coverRight: seq<bool>) returns (ok: bool)
  requires nLeft >= 0 && nRight >= 0
  requires |graph| == nLeft
  requires |coverLeft| == nLeft
  requires |coverRight| == nRight
  requires forall i :: 0 <= i < nLeft ==> |graph[i]| == nRight
{
  var i := 0;
  while i < nLeft
  {
    var j := 0;
    while j < nRight
    {
      if graph[i][j] && !coverLeft[i] && !coverRight[j] {
        return false;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return true;
}

method CountTrue(s: seq<bool>) returns (c: nat)
{
  c := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] { c := c + 1; }
    i := i + 1;
  }
}

method Main()
{
  // Test postcondition properties
  var ok := CheckCoverSpec([true, false], [false, true], 2, 2, 2);
  expect ok, "coverLeft=2, coverRight=2, coverSize=2, nLeft=2, nRight=2: valid";

  ok := CheckCoverSpec([false], [false], 0, 1, 1);
  expect ok, "Empty cover: valid";

  ok := CheckCoverSpec([], [], 0, 0, 0);
  expect ok, "Empty graph: valid";

  // Negative: wrong lengths
  ok := CheckCoverSpec([true], [false, true], 1, 2, 2);
  expect !ok, "|coverLeft|=1 != nLeft=2";

  ok := CheckCoverSpec([true, false], [false], 1, 2, 2);
  expect !ok, "|coverRight|=1 != nRight=2";

  // Negative: coverSize too large
  ok := CheckCoverSpec([true, false], [false, true], 5, 2, 2);
  expect !ok, "coverSize=5 > nLeft+nRight=4";

  // Test cover validity checker
  // Graph: left0-right0, left1-right1 (diagonal matching)
  // Cover: both left nodes
  var r := CheckCoverValid([[true, false], [false, true]], 2, 2,
                            [true, true], [false, false]);
  expect r, "Covering both left nodes covers all edges";

  // Cover: both right nodes
  r := CheckCoverValid([[true, false], [false, true]], 2, 2,
                        [false, false], [true, true]);
  expect r, "Covering both right nodes covers all edges";

  // Cover: no nodes (negative)
  r := CheckCoverValid([[true, false], [false, true]], 2, 2,
                        [false, false], [false, false]);
  expect !r, "Empty cover does not cover edges";

  // Cover: only one side for K(2,2) - needs at least one side covered
  r := CheckCoverValid([[true, true], [true, true]], 2, 2,
                        [true, true], [false, false]);
  expect r, "Covering all left nodes covers K(2,2)";

  r := CheckCoverValid([[true, true], [true, true]], 2, 2,
                        [true, false], [false, false]);
  expect !r, "Covering only left0 does not cover all edges in K(2,2)";

  // No edges: empty cover is valid
  r := CheckCoverValid([[false, false], [false, false]], 2, 2,
                        [false, false], [false, false]);
  expect r, "No edges: empty cover is valid";

  print "All spec tests passed\n";
}
