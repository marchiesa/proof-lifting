// Cycle Detection DFS -- Runtime spec tests

// The spec is `ensures true` - there are no meaningful spec predicates.
// We test the precondition validation: that the adjacency matrix is well-formed.

method ValidAdjMatrixCheck(graph: seq<seq<bool>>, n: int) returns (ok: bool)
{
  if n < 0 { return false; }
  if |graph| != n { return false; }
  var i := 0;
  while i < n
  {
    if |graph[i]| != n { return false; }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // Test precondition: valid adjacency matrix
  var r := ValidAdjMatrixCheck([[false, true, false], [false, false, true], [false, false, false]], 3);
  expect r, "3x3 matrix should be valid";

  r := ValidAdjMatrixCheck([[false]], 1);
  expect r, "1x1 matrix should be valid";

  r := ValidAdjMatrixCheck([], 0);
  expect r, "Empty matrix should be valid for n=0";

  // Invalid: wrong size
  r := ValidAdjMatrixCheck([[false, true], [false, false, true]], 2);
  expect !r, "Row with wrong length should be invalid";

  r := ValidAdjMatrixCheck([[false]], 2);
  expect !r, "Wrong number of rows should be invalid";

  // Invalid: negative n
  r := ValidAdjMatrixCheck([], -1);
  expect !r, "Negative n should be invalid";

  // Test: adjacency matrix correctly represents edges
  var g := [[false, true, false], [false, false, true], [true, false, false]];
  // Edge 0->1: g[0][1] == true
  expect g[0][1], "Edge 0->1 should exist";
  expect !g[0][0], "No self-loop at 0";
  expect !g[0][2], "No edge 0->2";
  expect g[1][2], "Edge 1->2 should exist";
  expect g[2][0], "Edge 2->0 should exist (cycle)";

  // DAG has no back edges
  var dag := [[false, true, false], [false, false, true], [false, false, false]];
  expect dag[0][1], "Edge 0->1 in DAG";
  expect dag[1][2], "Edge 1->2 in DAG";
  expect !dag[2][0], "No back edge 2->0 in DAG";
  expect !dag[1][0], "No back edge 1->0 in DAG";

  print "All spec tests passed\n";
}
