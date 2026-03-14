// Tarjan's Bridges -- Runtime spec tests

// The spec:
//   ensures forall k :: 0 <= k < |bridges| ==> 0 <= bridges[k].0 < n && 0 <= bridges[k].1 < n
// We test this postcondition and the symmetry precondition.

method CheckBridgesInRange(bridges: seq<(int,int)>, n: int) returns (ok: bool)
{
  var k := 0;
  while k < |bridges|
  {
    if bridges[k].0 < 0 || bridges[k].0 >= n { return false; }
    if bridges[k].1 < 0 || bridges[k].1 >= n { return false; }
    k := k + 1;
  }
  return true;
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
  // Test CheckBridgesInRange: valid bridges
  var r := CheckBridgesInRange([(0, 1), (1, 2)], 3);
  expect r, "Bridges [(0,1),(1,2)] should be in range [0,3)";

  r := CheckBridgesInRange([(0, 1)], 2);
  expect r, "Bridge (0,1) in range [0,2)";

  r := CheckBridgesInRange([], 5);
  expect r, "Empty bridges should be valid";

  // Invalid: endpoint out of range
  r := CheckBridgesInRange([(0, 3)], 3);
  expect !r, "Bridge (0,3) out of range [0,3)";

  r := CheckBridgesInRange([(-1, 0)], 3);
  expect !r, "Bridge (-1,0) out of range";

  r := CheckBridgesInRange([(0, 1), (1, 5)], 3);
  expect !r, "Second bridge (1,5) out of range";

  // Test symmetry check
  r := SymmetricCheck([[false, true, false], [true, false, true], [false, true, false]], 3);
  expect r, "Path graph 0-1-2 is symmetric";

  r := SymmetricCheck([[false, true, true], [true, false, true], [true, true, false]], 3);
  expect r, "Triangle is symmetric";

  r := SymmetricCheck([[false, true], [false, false]], 2);
  expect !r, "Directed edge 0->1 only is not symmetric";

  r := SymmetricCheck([[false]], 1);
  expect r, "Single node is symmetric";

  r := SymmetricCheck([], 0);
  expect r, "Empty graph is symmetric";

  // Test that expected bridge tuples have correct format
  var bridge := (1, 3);
  expect bridge.0 == 1 && bridge.1 == 3, "Bridge tuple access works";

  print "All spec tests passed\n";
}
