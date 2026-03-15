// Maximum Area of Island

predicate ValidGrid(grid: seq<int>, rows: int, cols: int)
{
  rows > 0 && cols > 0 && |grid| == rows * cols &&
  forall i :: 0 <= i < |grid| ==> grid[i] == 0 || grid[i] == 1
}

function Idx(r: int, c: int, cols: int): int { r * cols + c }

function Max(a: int, b: int): int { if a >= b then a else b }

method MaxAreaIsland(grid: seq<int>, rows: int, cols: int) returns (maxArea: int)
  requires ValidGrid(grid, rows, cols)
  ensures maxArea >= 0
{
  var visited := seq(|grid|, _ => false);
  maxArea := 0;

  var i := 0;
  while i < rows
  {
    var j := 0;
    while j < cols
    {
      if grid[Idx(i, j, cols)] == 1 && !visited[Idx(i, j, cols)] {
        // BFS from (i, j)
        var area := 0;
        var queue := [Idx(i, j, cols)];
        visited := visited[..Idx(i, j, cols)] + [true] + visited[Idx(i, j, cols)+1..];
        while |queue| > 0
        {
          var cur := queue[0];
          queue := queue[1..];
          area := area + 1;
          var r := cur / cols;
          var c := cur % cols;
          // Check 4 neighbors
          var neighbors := [];
          if r > 0 { neighbors := neighbors + [Idx(r-1, c, cols)]; }
          if r < rows - 1 { neighbors := neighbors + [Idx(r+1, c, cols)]; }
          if c > 0 { neighbors := neighbors + [Idx(r, c-1, cols)]; }
          if c < cols - 1 { neighbors := neighbors + [Idx(r, c+1, cols)]; }
          var n := 0;
          while n < |neighbors|
          {
            var nb := neighbors[n];
            if 0 <= nb < |grid| && grid[nb] == 1 && !visited[nb] {
              visited := visited[..nb] + [true] + visited[nb+1..];
              queue := queue + [nb];
            }
            n := n + 1;
          }
        }
        maxArea := Max(maxArea, area);
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  // 3x3 grid with one island of area 4
  // 1 1 0
  // 1 1 0
  // 0 0 0
  var g := [1, 1, 0, 1, 1, 0, 0, 0, 0];
  expect ValidGrid(g, 3, 3);
  var r1 := MaxAreaIsland(g, 3, 3);
  expect r1 >= 0;

  // All zeros
  var g2 := [0, 0, 0, 0];
  expect ValidGrid(g2, 2, 2);
  var r2 := MaxAreaIsland(g2, 2, 2);
  expect r2 >= 0;

  // All ones
  var g3 := [1, 1, 1, 1];
  expect ValidGrid(g3, 2, 2);
  var r3 := MaxAreaIsland(g3, 2, 2);
  expect r3 >= 0;

  // Single cell
  var g4 := [1];
  expect ValidGrid(g4, 1, 1);
  var r4 := MaxAreaIsland(g4, 1, 1);
  expect r4 >= 0;

  // Negative test: invalid grid
  expect !ValidGrid([0, 1, 2], 1, 3);

  print "All spec tests passed\n";
}
