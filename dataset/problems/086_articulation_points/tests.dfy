// Articulation Points -- Runtime spec tests

// The spec: ensures |isAP| == n
// We test this postcondition and the symmetry precondition.

method CheckAPSpec(isAP: seq<bool>, n: int) returns (ok: bool)
{
  ok := |isAP| == n;
}

method SymmetricCheck(graph: seq<seq<bool>>, n: int) returns (ok: bool)
{
  if n < 0 || |graph| != n { return false; }
  var i := 0;
  while i < n
  {
    if |graph[i]| != n { return false; }
    i := i + 1;
  }
  i := 0;
  while i < n
  {
    var j := 0;
    while j < n
    {
      if j < |graph| && |graph[j]| == n && i < |graph| && |graph[i]| == n {
        if graph[i][j] != graph[j][i] { return false; }
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // Test postcondition: |isAP| == n
  var ok := CheckAPSpec([false, true, false], 3);
  expect ok, "|isAP|=3 matches n=3";

  ok := CheckAPSpec([false], 1);
  expect ok, "|isAP|=1 matches n=1";

  ok := CheckAPSpec([], 0);
  expect ok, "|isAP|=0 matches n=0";

  // Negative: wrong length
  ok := CheckAPSpec([false, true], 3);
  expect !ok, "|isAP|=2 != n=3";

  ok := CheckAPSpec([false], 0);
  expect !ok, "|isAP|=1 != n=0";

  // Test symmetry precondition
  // Path graph 0-1-2 (symmetric)
  var r := SymmetricCheck([[false, true, false], [true, false, true], [false, true, false]], 3);
  expect r, "Path graph 0-1-2 is symmetric";

  // Triangle (symmetric)
  r := SymmetricCheck([[false, true, true], [true, false, true], [true, true, false]], 3);
  expect r, "Triangle is symmetric";

  // Star graph center=0 (symmetric)
  r := SymmetricCheck([
    [false, true, true, true],
    [true, false, false, false],
    [true, false, false, false],
    [true, false, false, false]
  ], 4);
  expect r, "Star graph is symmetric";

  // Not symmetric
  r := SymmetricCheck([[false, true], [false, false]], 2);
  expect !r, "Directed edge is not symmetric";

  // Test expected AP results as boolean sequences
  // Path 0-1-2: node 1 is AP
  var ap := [false, true, false];
  expect !ap[0] && ap[1] && !ap[2], "In path 0-1-2, only node 1 is AP";

  // Triangle: no APs
  var apTriangle := [false, false, false];
  expect !apTriangle[0] && !apTriangle[1] && !apTriangle[2], "Triangle has no APs";

  // Star: center is AP
  var apStar := [true, false, false, false];
  expect apStar[0], "Star center should be AP";
  expect !apStar[1] && !apStar[2] && !apStar[3], "Star leaves should not be APs";

  print "All spec tests passed\n";
}
