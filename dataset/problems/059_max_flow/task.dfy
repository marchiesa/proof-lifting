// Max Flow (bounded Ford-Fulkerson with BFS augmenting paths)
// Task: Add loop invariants so that Dafny can verify this program.
// Simplified: finds maximum flow value in a graph with capacity matrix.

method MaxFlow(n: int, cap: array2<int>, source: int, sink: int) returns (flow: int)
  requires n > 0
  requires cap.Length0 == n && cap.Length1 == n
  requires 0 <= source < n && 0 <= sink < n && source != sink
  requires forall i, j :: 0 <= i < n && 0 <= j < n ==> cap[i, j] >= 0
  modifies cap
  ensures flow >= 0
{
  flow := 0;

  var iterations := n * n;
  while iterations > 0
  {
    // BFS to find augmenting path from source to sink
    var parent := new int[n];
    var visited := new bool[n];
    var i := 0;
    while i < n
    {
      parent[i] := -1;
      visited[i] := false;
      i := i + 1;
    }
    visited[source] := true;

    var found := false;
    var bfs_fuel := n * n;
    var queue_start := 0;
    var queue := new int[n];
    var queue_end := 1;
    queue[0] := source;

    while queue_start < queue_end && !found && bfs_fuel > 0
    {
      var u := queue[queue_start];
      queue_start := queue_start + 1;
      if 0 <= u < n {
        var v := 0;
        while v < n && !found
        {
          if !visited[v] && cap[u, v] > 0 && queue_end < n {
            parent[v] := u;
            visited[v] := true;
            if v == sink {
              found := true;
            } else {
              queue[queue_end] := v;
              queue_end := queue_end + 1;
            }
          }
          v := v + 1;
        }
      }
      bfs_fuel := bfs_fuel - 1;
    }

    if !found {
      break;
    }

    // Walk parent chain to find bottleneck capacity
    var bottleneck_raw := cap[parent[sink], sink];
    var bottleneck := if bottleneck_raw > 0 then bottleneck_raw else 0;
    var cur := sink;
    var walk_fuel := n;
    while cur != source && walk_fuel > 0 && parent[cur] >= 0
    {
      var p := parent[cur];
      if cap[p, cur] >= 0 && cap[p, cur] < bottleneck {
        bottleneck := cap[p, cur];
      } else if cap[p, cur] < 0 {
        bottleneck := 0;
      }
      cur := p;
      walk_fuel := walk_fuel - 1;
    }

    if bottleneck > 0 {
      // Update residual capacities along path
      cur := sink;
      walk_fuel := n;
      while cur != source && walk_fuel > 0 && parent[cur] >= 0
      {
        var p := parent[cur];
        cap[p, cur] := cap[p, cur] - bottleneck;
        cap[cur, p] := cap[cur, p] + bottleneck;
        cur := p;
        walk_fuel := walk_fuel - 1;
      }

      flow := flow + bottleneck;
    } else {
      break;
    }

    iterations := iterations - 1;
  }
}
