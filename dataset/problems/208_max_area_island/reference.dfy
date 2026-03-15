// Maximum Area of Island -- Reference solution with invariants

predicate ValidGrid(grid: seq<int>, rows: int, cols: int)
{
  rows > 0 && cols > 0 && |grid| == rows * cols &&
  forall i :: 0 <= i < |grid| ==> grid[i] == 0 || grid[i] == 1
}

function Max(a: int, b: int): int { if a >= b then a else b }

method MaxAreaIsland(grid: seq<int>, rows: int, cols: int) returns (maxArea: int)
  requires ValidGrid(grid, rows, cols)
  ensures maxArea >= 0
{
  var visited := seq(|grid|, _ => false);
  maxArea := 0;

  var i := 0;
  while i < |grid|
    invariant 0 <= i <= |grid|
    invariant |visited| == |grid|
    invariant maxArea >= 0
    decreases |grid| - i
  {
    if grid[i] == 1 && !visited[i] {
      // BFS from cell i
      var area := 0;
      var queue := [i];
      visited := visited[i := true];
      var fuel := |grid|;
      while |queue| > 0 && fuel > 0
        invariant |visited| == |grid|
        invariant area >= 0
        invariant forall q :: q in queue ==> 0 <= q < |grid|
        decreases fuel
      {
        assert queue[0] in queue;
        var cur := queue[0];
        ghost var oldQueue := queue;
        queue := queue[1..];
        // All elements of queue[1..] were in oldQueue
        assert forall q :: q in queue ==> q in oldQueue;
        area := area + 1;
        fuel := fuel - 1;
        // Add unvisited land neighbors
        var r := cur / cols;
        var c := cur % cols;
        var nbrs: seq<int> := [];
        if r > 0 { nbrs := nbrs + [cur - cols]; }
        if r < rows - 1 { nbrs := nbrs + [cur + cols]; }
        if c > 0 { nbrs := nbrs + [cur - 1]; }
        if c < cols - 1 { nbrs := nbrs + [cur + 1]; }
        assert forall q :: q in queue ==> 0 <= q < |grid|;
        var n := 0;
        while n < |nbrs|
          invariant 0 <= n <= |nbrs|
          invariant |visited| == |grid|
          invariant forall q :: q in queue ==> 0 <= q < |grid|
          decreases |nbrs| - n
        {
          var nb := nbrs[n];
          if 0 <= nb < |grid| && grid[nb] == 1 && !visited[nb] {
            visited := visited[nb := true];
            queue := queue + [nb];
          }
          n := n + 1;
        }
      }
      maxArea := Max(maxArea, area);
    }
    i := i + 1;
  }
}
