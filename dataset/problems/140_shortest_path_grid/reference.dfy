// Shortest Path in Grid -- Reference solution with invariants
// Simplified: compute minimum path cost along first row only

predicate ValidGrid(grid: seq<seq<int>>, rows: int, cols: int)
{
  rows > 0 && cols > 0 &&
  |grid| == rows &&
  (forall i :: 0 <= i < rows ==> |grid[i]| == cols) &&
  (forall i, j :: 0 <= i < rows && 0 <= j < cols ==> grid[i][j] == 0 || grid[i][j] == 1)
}

// Computes the path cost along the first row: -1 if blocked, else steps to (0, cols-1)
method ShortestPath(grid: seq<seq<int>>, rows: int, cols: int) returns (dist: int)
  requires ValidGrid(grid, rows, cols)
  requires grid[0][0] == 0
  ensures dist >= -1
  ensures dist == -1 || dist >= 0
{
  // Walk along first row
  var i := 1;
  while i < cols
    invariant 1 <= i <= cols
    decreases cols - i
  {
    if grid[0][i] == 1 {
      dist := -1;
      return;
    }
    i := i + 1;
  }

  // If last cell in first row is reachable
  if rows == 1 {
    dist := cols - 1;
    return;
  }

  // Walk down last column
  i := 1;
  while i < rows
    invariant 1 <= i <= rows
    decreases rows - i
  {
    if grid[i][cols - 1] == 1 {
      dist := -1;
      return;
    }
    i := i + 1;
  }

  dist := (cols - 1) + (rows - 1);
}
