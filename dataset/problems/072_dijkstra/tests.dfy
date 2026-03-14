// Dijkstra -- Runtime spec tests

// Bounded compilable versions of spec predicates
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
      j := j + 1;
    }
    i := i + 1;
  }
  return true;
}

method NonNegWeightsCheck(graph: seq<seq<int>>, n: int) returns (result: bool)
  requires |graph| == n
  requires n >= 0
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
{
  var i := 0;
  while i < n
  {
    var j := 0;
    while j < n
    {
      if graph[i][j] != -1 && graph[i][j] < 0 { return false; }
      j := j + 1;
    }
    i := i + 1;
  }
  return true;
}

method CheckDistSpec(dist: seq<int>, n: int, src: int) returns (ok: bool)
  requires |dist| == n
  requires 0 <= src < n
{
  // dist[src] >= 0
  if dist[src] < 0 { return false; }
  // forall i: dist[i] >= -1
  var i := 0;
  while i < n
  {
    if dist[i] < -1 { return false; }
    // if dist[i] != -1 then dist[i] >= 0
    if dist[i] != -1 && dist[i] < 0 { return false; }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // Test ValidGraph predicate
  var g1: seq<seq<int>> := [[0, 1, 5], [-1, 0, 2], [-1, -1, 0]];
  var r := ValidGraphCheck(g1, 3);
  expect r, "Simple 3-node graph should be valid";

  // Invalid: wrong dimensions
  var g2: seq<seq<int>> := [[0, 1], [-1, 0, 2]];
  r := ValidGraphCheck(g2, 3);
  expect !r, "Mismatched dimensions should be invalid";

  // Invalid: weight below -1
  var g3: seq<seq<int>> := [[0, -2], [-1, 0]];
  r := ValidGraphCheck(g3, 2);
  expect !r, "Weight -2 should be invalid";

  // Test NonNegWeights
  r := NonNegWeightsCheck([[0, 1, 5], [-1, 0, 2], [-1, -1, 0]], 3);
  expect r, "All non -1 weights are >= 0";

  // Test dist spec checking
  // Valid: source dist 0, others reachable
  r := CheckDistSpec([0, 1, 3], 3, 0);
  expect r, "Valid dist from source 0";

  // Valid: unreachable node (-1)
  r := CheckDistSpec([0, 1, -1], 3, 0);
  expect r, "Unreachable node has -1 dist";

  // Invalid: source distance negative
  r := CheckDistSpec([-1, 1, 3], 3, 0);
  expect !r, "Source with dist -1 should fail";

  // Invalid: distance below -1
  r := CheckDistSpec([0, -2, 3], 3, 0);
  expect !r, "Dist -2 should fail";

  print "All spec tests passed\n";
}
