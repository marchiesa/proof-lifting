// Maximum Area of Island -- Reference solution with invariants

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
    invariant 0 <= i <= rows
    invariant |visited| == |grid|
    invariant maxArea >= 0
    decreases rows - i
  {
    var j := 0;
    while j < cols
      invariant 0 <= j <= cols
      invariant |visited| == |grid|
      invariant maxArea >= 0
      decreases cols - j
    {
      var idx := Idx(i, j, cols);
      assert 0 <= idx < |grid| by {
        assert i * cols + j < rows * cols;
      }
      if grid[idx] == 1 && !visited[idx] {
        var area := 0;
        var queue := [idx];
        visited := visited[..idx] + [true] + visited[idx+1..];
        while |queue| > 0
          invariant |visited| == |grid|
          invariant area >= 0
          invariant forall q :: q in queue ==> 0 <= q < |grid|
          decreases |grid| - area
        {
          var cur := queue[0];
          queue := queue[1..];
          area := area + 1;
          var r := cur / cols;
          var c := cur % cols;
          var neighbors: seq<int> := [];
          if r > 0 { neighbors := neighbors + [Idx(r-1, c, cols)]; }
          if r < rows - 1 { neighbors := neighbors + [Idx(r+1, c, cols)]; }
          if c > 0 { neighbors := neighbors + [Idx(r, c-1, cols)]; }
          if c < cols - 1 { neighbors := neighbors + [Idx(r, c+1, cols)]; }
          var n := 0;
          while n < |neighbors|
            invariant 0 <= n <= |neighbors|
            invariant |visited| == |grid|
            invariant forall q :: q in queue ==> 0 <= q < |grid|
            decreases |neighbors| - n
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
