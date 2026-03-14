// BFS Shortest Path -- Runtime spec tests

// The spec ensures:
//   |dist| == n
//   dist[src] >= 0
//   forall i :: 0 <= i < n ==> dist[i] >= -1

method CheckBFSSpec(dist: seq<int>, n: int, src: int) returns (ok: bool)
  requires |dist| == n
  requires 0 <= src < n
{
  if dist[src] < 0 { return false; }
  var i := 0;
  while i < n
  {
    if dist[i] < -1 { return false; }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // Valid BFS result: linear graph 0->1->2, source 0
  var r := CheckBFSSpec([0, 1, 2], 3, 0);
  expect r, "Valid BFS result [0,1,2] from source 0";

  // Valid: unreachable node
  r := CheckBFSSpec([0, 1, -1], 3, 0);
  expect r, "Unreachable node has -1";

  // Valid: all unreachable except source
  r := CheckBFSSpec([0, -1, -1], 3, 0);
  expect r, "Only source reachable";

  // Valid: source in the middle
  r := CheckBFSSpec([1, 0, 1], 3, 1);
  expect r, "Source at index 1, dist [1,0,1]";

  // Valid: single node
  r := CheckBFSSpec([0], 1, 0);
  expect r, "Single node graph";

  // Invalid: source distance < 0
  r := CheckBFSSpec([-1, 0, 1], 3, 0);
  expect !r, "Source dist -1 should fail";

  // Invalid: distance < -1
  r := CheckBFSSpec([0, -2, 1], 3, 0);
  expect !r, "Dist -2 should fail";

  // Invalid: all negative including source
  r := CheckBFSSpec([-1, -1, -1], 3, 0);
  expect !r, "All -1 including source should fail";

  print "All spec tests passed\n";
}
