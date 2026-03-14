// Tarjan's Bridges Finding
// Task: Add loop invariants so that Dafny can verify this program.

method FindBridges(graph: seq<seq<bool>>, n: int) returns (bridges: seq<(int,int)>)
  requires n >= 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  requires forall i, j :: 0 <= i < n && 0 <= j < n ==> graph[i][j] == graph[j][i]
  ensures forall k :: 0 <= k < |bridges| ==> 0 <= bridges[k].0 < n && 0 <= bridges[k].1 < n
{
  var disc := seq(n, _ => -1);
  var low := seq(n, _ => -1);
  bridges := [];
  var timer := 0;
  var i := 0;
  while i < n
  {
    if disc[i] == -1 {
      // DFS from i
      var stack: seq<(int, int, int)> := [(i, -1, 0)]; // (node, parent, nextNeighbor)
      disc := disc[i := timer];
      low := low[i := timer];
      timer := timer + 1;
      var fuel := n * n;
      while |stack| > 0 && fuel > 0
      {
        var top := stack[|stack| - 1];
        var u := top.0;
        var par := top.1;
        var j := top.2;
        if j >= n {
          // Done with u, update parent's low
          stack := stack[..|stack| - 1];
          if |stack| > 0 {
            var pTop := stack[|stack| - 1];
            var pU := pTop.0;
            if low[u] < low[pU] {
              low := low[pU := low[u]];
            }
            if low[u] > disc[pU] {
              bridges := bridges + [(pU, u)];
            }
          }
        } else {
          stack := stack[..|stack| - 1] + [(u, par, j + 1)];
          if graph[u][j] && j != par {
            if disc[j] == -1 {
              disc := disc[j := timer];
              low := low[j := timer];
              timer := timer + 1;
              stack := stack + [(j, u, 0)];
            } else if disc[j] >= 0 && disc[j] < low[u] {
              low := low[u := disc[j]];
            }
          }
        }
        fuel := fuel - 1;
      }
    }
    i := i + 1;
  }
}
