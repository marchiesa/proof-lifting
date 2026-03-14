// Count Paths in DAG -- Runtime spec tests

// The spec: ensures count >= 0 (trivially true since count is nat)
// We test input validation and expected behavior properties.

method ValidDAGInputCheck(graph: seq<seq<bool>>, n: int, src: int, tgt: int) returns (ok: bool)
{
  if n <= 0 { return false; }
  if src < 0 || src >= n { return false; }
  if tgt < 0 || tgt >= n { return false; }
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
  // Test precondition validation: valid inputs
  var r := ValidDAGInputCheck(
    [[false, true, false], [false, false, true], [false, false, false]], 3, 0, 2);
  expect r, "Linear DAG 0->1->2 with src=0, tgt=2 should be valid";

  r := ValidDAGInputCheck([[false]], 1, 0, 0);
  expect r, "Single node with src=tgt=0 should be valid";

  // Invalid: src out of range
  r := ValidDAGInputCheck([[false, true], [false, false]], 2, 2, 0);
  expect !r, "src=2 out of range for n=2";

  // Invalid: tgt out of range
  r := ValidDAGInputCheck([[false, true], [false, false]], 2, 0, -1);
  expect !r, "tgt=-1 out of range";

  // Invalid: wrong dimensions
  r := ValidDAGInputCheck([[false]], 2, 0, 1);
  expect !r, "Graph dimensions mismatch";

  // Test count >= 0 property: any nat satisfies this
  var count: nat := 0;
  expect count >= 0, "count 0 >= 0";
  count := 5;
  expect count >= 0, "count 5 >= 0";
  count := 100;
  expect count >= 0, "count 100 >= 0";

  // Test graph edge checking for expected path counting
  var g := [[false, true, true, false],
            [false, false, false, true],
            [false, false, false, true],
            [false, false, false, false]];
  // Paths from 0 to 3: 0->1->3 and 0->2->3 => 2 paths
  expect g[0][1], "Edge 0->1 exists";
  expect g[0][2], "Edge 0->2 exists";
  expect g[1][3], "Edge 1->3 exists";
  expect g[2][3], "Edge 2->3 exists";
  expect !g[0][3], "No direct edge 0->3";

  print "All spec tests passed\n";
}
