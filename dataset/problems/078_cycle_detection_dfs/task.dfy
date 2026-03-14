// Cycle Detection in Directed Graph (DFS Coloring)
// Task: Add loop invariants so that Dafny can verify this program.
// Uses iterative DFS with explicit stack and 3-color scheme.
// Color: 0 = white (unvisited), 1 = gray (in stack), 2 = black (done)

method HasCycle(graph: seq<seq<bool>>, n: int) returns (hasCycle: bool)
  requires n >= 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  ensures true
{
  var color := seq(n, _ => 0);
  hasCycle := false;
  var start := 0;
  while start < n
  {
    if color[start] == 0 {
      color := color[start := 1];
      var stackNode: seq<int> := [start];
      var stackNext: seq<int> := [0];
      var fuel := n * (n + 1);
      while |stackNode| > 0 && fuel > 0
      {
        var u := stackNode[|stackNode| - 1];
        var nextJ := stackNext[|stackNext| - 1];
        if nextJ >= n {
          color := color[u := 2];
          stackNode := stackNode[..|stackNode| - 1];
          stackNext := stackNext[..|stackNext| - 1];
        } else {
          stackNext := stackNext[..|stackNext| - 1] + [nextJ + 1];
          if graph[u][nextJ] {
            if color[nextJ] == 1 {
              hasCycle := true;
              return;
            } else if color[nextJ] == 0 {
              color := color[nextJ := 1];
              stackNode := stackNode + [nextJ];
              stackNext := stackNext + [0];
            }
          }
        }
        fuel := fuel - 1;
      }
    }
    start := start + 1;
  }
}
