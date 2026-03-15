// Shortest Path in Grid
// Task: Add loop invariants so that Dafny can verify this program.
// Computes path cost along first row then last column.

predicate ValidGrid(grid: seq<seq<int>>, rows: int, cols: int)
{
  rows > 0 && cols > 0 &&
  |grid| == rows &&
  (forall i :: 0 <= i < rows ==> |grid[i]| == cols) &&
  (forall i, j :: 0 <= i < rows && 0 <= j < cols ==> grid[i][j] == 0 || grid[i][j] == 1)
}

method ShortestPath(grid: seq<seq<int>>, rows: int, cols: int) returns (dist: int)
  requires ValidGrid(grid, rows, cols)
  requires grid[0][0] == 0
  ensures dist >= -1
  ensures dist == -1 || dist >= 0
{
  var i := 1;
  while i < cols
    // invariant
  {
    if grid[0][i] == 1 {
      dist := -1;
      return;
    }
    i := i + 1;
  }

  if rows == 1 {
    dist := cols - 1;
    return;
  }

  i := 1;
  while i < rows
    // invariant
  {
    if grid[i][cols - 1] == 1 {
      dist := -1;
      return;
    }
    i := i + 1;
  }

  dist := (cols - 1) + (rows - 1);
}
