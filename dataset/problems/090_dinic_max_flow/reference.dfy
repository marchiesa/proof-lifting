// Dinic's Max Flow -- Reference solution with invariants

method DinicMaxFlow(cap: array2<int>, n: int, src: int, sink: int) returns (maxFlow: int)
  requires n > 0
  requires 0 <= src < n && 0 <= sink < n && src != sink
  requires cap.Length0 == n && cap.Length1 == n
  requires forall i, j :: 0 <= i < n && 0 <= j < n ==> cap[i, j] >= 0
  modifies cap
  ensures maxFlow >= 0
{
  maxFlow := 0;
  var fuel := n * n;
  while fuel > 0
    invariant maxFlow >= 0
    decreases fuel
  {
    // BFS to build level graph
    var level := new int[n](_ => -1);
    level[src] := 0;
    var queue := new int[n];
    queue[0] := src;
    var qLen := 1;
    var head := 0;
    while head < qLen
      invariant 0 <= head <= qLen <= n
      invariant forall k :: 0 <= k < qLen ==> 0 <= queue[k] < n
      decreases n - head
    {
      var u := queue[head];
      head := head + 1;
      var j := 0;
      while j < n
        invariant 0 <= j <= n
        invariant 0 <= head <= qLen <= n
        invariant forall k :: 0 <= k < qLen ==> 0 <= queue[k] < n
        decreases n - j
      {
        if cap[u, j] > 0 && level[j] == -1 && qLen < n {
          level[j] := level[u] + 1;
          queue[qLen] := j;
          qLen := qLen + 1;
        }
        j := j + 1;
      }
    }
    if level[sink] == -1 { break; }
    // Send blocking flow
    var blockFuel := n * n;
    while blockFuel > 0
      invariant maxFlow >= 0
      decreases blockFuel
    {
      // DFS to find augmenting path in level graph
      var path := new int[n](_ => -1);
      var visited := new bool[n](_ => false);
      var stack: seq<int> := [src];
      visited[src] := true;
      var found := false;
      var pathFuel := n;
      while |stack| > 0 && !found && pathFuel > 0
        invariant forall k :: 0 <= k < |stack| ==> 0 <= stack[k] < n
        decreases pathFuel
      {
        var u := stack[|stack| - 1];
        if u == sink {
          found := true;
        } else {
          var pushed := false;
          var j := 0;
          while j < n && !pushed
            invariant 0 <= j <= n
            invariant forall k :: 0 <= k < |stack| ==> 0 <= stack[k] < n
            decreases n - j
          {
            if cap[u, j] > 0 && level[j] == level[u] + 1 && !visited[j] {
              visited[j] := true;
              path[j] := u;
              stack := stack + [j];
              pushed := true;
            }
            j := j + 1;
          }
          if !pushed {
            if |stack| > 0 {
              stack := stack[..|stack| - 1];
            }
          }
        }
        pathFuel := pathFuel - 1;
      }
      if !found { break; }
      // Find bottleneck
      var bottleneck := 1;
      if path[sink] >= 0 && path[sink] < n {
        bottleneck := cap[path[sink], sink];
        if bottleneck <= 0 { bottleneck := 1; }
      }
      // Update residual graph along path
      var v := sink;
      var steps := n;
      while v != src && steps > 0 && 0 <= v < n && path[v] >= 0 && path[v] < n
        invariant maxFlow >= 0
        invariant steps >= 0
        decreases steps
      {
        var pv := path[v];
        cap[pv, v] := cap[pv, v] - bottleneck;
        cap[v, pv] := cap[v, pv] + bottleneck;
        v := pv;
        steps := steps - 1;
      }
      maxFlow := maxFlow + bottleneck;
      blockFuel := blockFuel - 1;
    }
    fuel := fuel - 1;
  }
}
