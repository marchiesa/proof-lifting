// Prim's MST -- Runtime spec tests

// Bounded compilable version of ValidGraph - checks all conditions
method ValidGraphCheck(graph: seq<seq<int>>, n: int) returns (result: bool)
{
  if n < 0 || |graph| != n { return false; }
  var i := 0;
  while i < n
  {
    if |graph[i]| != n { return false; }
    var j := 0;
    while j < n
    {
      if graph[i][j] < -1 { return false; }
      // Check symmetry (only safe because we confirmed |graph[i]| == n above
      // and we need to confirm |graph[j]| == n too)
      if |graph[j]| != n { return false; }
      if graph[i][j] != graph[j][i] { return false; }
      j := j + 1;
    }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // Test ValidGraph: valid symmetric graph
  var g1: seq<seq<int>> := [[-1, 1, 3], [1, -1, 2], [3, 2, -1]];
  var r := ValidGraphCheck(g1, 3);
  expect r, "Triangle graph should be valid";

  // Test ValidGraph: invalid (not symmetric)
  var g2: seq<seq<int>> := [[-1, 1, 3], [2, -1, 2], [3, 2, -1]];
  r := ValidGraphCheck(g2, 3);
  expect !r, "Non-symmetric graph should be invalid";

  // Test ValidGraph: invalid (weight < -1)
  var g3: seq<seq<int>> := [[-1, -2], [-2, -1]];
  r := ValidGraphCheck(g3, 2);
  expect !r, "Weight -2 should be invalid";

  // Test ValidGraph: single node
  var g4: seq<seq<int>> := [[-1]];
  r := ValidGraphCheck(g4, 1);
  expect r, "Single node graph should be valid";

  // Test ValidGraph: wrong dimensions
  var g5: seq<seq<int>> := [[-1, 1], [1, -1, 2]];
  r := ValidGraphCheck(g5, 2);
  expect !r, "Wrong row length should be invalid";

  // Test ValidGraph: n=0
  var g6: seq<seq<int>> := [];
  r := ValidGraphCheck(g6, 0);
  expect r, "Empty graph should be valid";

  // Test spec: totalWeight >= -1 on various values
  var w := 3;
  expect w >= -1, "MST weight 3 satisfies >= -1";
  w := -1;
  expect w >= -1, "Disconnected MST weight -1 satisfies >= -1";
  w := 0;
  expect w >= -1, "MST weight 0 satisfies >= -1";

  // Negative: totalWeight < -1 would violate spec
  w := -2;
  expect !(w >= -1), "Weight -2 should violate totalWeight >= -1";

  print "All spec tests passed\n";
}
