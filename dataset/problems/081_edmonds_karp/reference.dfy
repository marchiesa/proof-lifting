// Edmonds-Karp Max Flow -- Reference solution with invariants

method EdmondsKarp(cap: array2<int>, n: int, src: int, sink: int) returns (maxFlow: int)
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
    // BFS to find augmenting path
    var parent := new int[n](_ => -1);
    var visited := new bool[n](_ => false);
    visited[src] := true;
    var queue := new int[n];
    queue[0] := src;
    var qLen := 1;
    var head := 0;
    var found := false;
    while head < qLen
      invariant 0 <= head <= qLen <= n
      invariant forall k :: 0 <= k < qLen ==> 0 <= queue[k] < n
      invariant forall i :: 0 <= i < n && parent[i] >= 0 ==> 0 <= parent[i] < n
      invariant forall k :: 0 <= k < qLen ==> visited[queue[k]]
      decreases n - head
    {
      var u := queue[head];
      head := head + 1;
      if u == sink { found := true; break; }
      var j := 0;
      while j < n
        invariant 0 <= j <= n
        invariant 0 <= head <= qLen <= n
        invariant forall k :: 0 <= k < qLen ==> 0 <= queue[k] < n
        invariant forall k :: 0 <= k < qLen ==> visited[queue[k]]
        invariant forall i :: 0 <= i < n && parent[i] >= 0 ==> 0 <= parent[i] < n
        decreases n - j
      {
        if !visited[j] && cap[u, j] > 0 && qLen < n {
          visited[j] := true;
          parent[j] := u;
          queue[qLen] := j;
          qLen := qLen + 1;
        }
        j := j + 1;
      }
    }
    if !found { break; }
    // Find bottleneck along path from sink to src
    // We need parent[sink] to be valid
    if parent[sink] < 0 || parent[sink] >= n { break; }
    var bottleneck := cap[parent[sink], sink];
    var v := sink;
    var steps := n;
    while v != src && steps > 0 && parent[v] >= 0
      invariant 0 <= v < n
      invariant steps >= 0
      decreases steps
    {
      var pv := parent[v];
      if 0 <= pv < n {
        if cap[pv, v] < bottleneck {
          bottleneck := cap[pv, v];
        }
        v := pv;
      } else {
        break;
      }
      steps := steps - 1;
    }
    if bottleneck <= 0 { fuel := fuel - 1; continue; }
    // Update residual graph along the path
    v := sink;
    steps := n;
    while v != src && steps > 0 && parent[v] >= 0
      invariant 0 <= v < n
      invariant steps >= 0
      decreases steps
    {
      var pv := parent[v];
      if 0 <= pv < n {
        cap[pv, v] := cap[pv, v] - bottleneck;
        cap[v, pv] := cap[v, pv] + bottleneck;
        v := pv;
      } else {
        break;
      }
      steps := steps - 1;
    }
    maxFlow := maxFlow + bottleneck;
    fuel := fuel - 1;
  }
}
