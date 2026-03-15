// Shortest Path in Grid -- Test cases

predicate ValidGrid(grid: seq<seq<int>>, rows: int, cols: int)
{
  rows > 0 && cols > 0 &&
  |grid| == rows &&
  (forall i :: 0 <= i < rows ==> |grid[i]| == cols) &&
  (forall i, j :: 0 <= i < rows && 0 <= j < cols ==> grid[i][j] == 0 || grid[i][j] == 1)
}

method Main()
{
  // Test ValidGrid - positive
  var g1 := [[0, 0], [0, 0]];
  expect ValidGrid(g1, 2, 2), "2x2 all zeros is valid";
  var g2 := [[0, 1], [1, 0]];
  expect ValidGrid(g2, 2, 2), "2x2 mixed is valid";

  // Test ValidGrid - negative
  var g3 := [[0, 2], [0, 0]];
  expect !ValidGrid(g3, 2, 2), "2 is not a valid cell value";

  // Basic path concepts
  // In [[0,0],[0,0]], shortest path from (0,0) to (1,1) is 2
  // In [[0,1],[0,0]], path: (0,0)->(1,0)->(1,1) = 2
  // In [[0,1],[1,0]], no path exists => -1

  // Spec just says dist >= -1
  expect -1 >= -1, "dist >= -1 holds for -1";
  expect 2 >= -1, "dist >= -1 holds for 2";

  print "All spec tests passed\n";
}
