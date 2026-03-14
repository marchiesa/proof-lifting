// BFS Shortest Path in Unweighted Graph -- Reference solution with invariants

method BFS(graph: seq<seq<bool>>, n: int, src: int) returns (dist: seq<int>)
  requires n > 0
  requires 0 <= src < n
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  ensures |dist| == n
  ensures dist[src] >= 0
  ensures forall i :: 0 <= i < n ==> dist[i] >= -1
{
  dist := seq(n, i => if i == src then 0 else -1);
  var queue := new int[n];
  queue[0] := src;
  var qLen := 1;
  var head := 0;
  while head < qLen
    invariant 0 <= head <= qLen <= n
    invariant |dist| == n
    invariant dist[src] >= 0
    invariant forall i :: 0 <= i < n ==> dist[i] >= -1
    invariant forall k :: 0 <= k < qLen ==> 0 <= queue[k] < n
    invariant forall k :: 0 <= k < qLen ==> dist[queue[k]] >= 0
    decreases n - head
  {
    var u := queue[head];
    head := head + 1;
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |dist| == n
      invariant 0 <= head <= qLen <= n
      invariant dist[src] >= 0
      invariant forall i :: 0 <= i < n ==> dist[i] >= -1
      invariant forall k :: 0 <= k < qLen ==> 0 <= queue[k] < n
      invariant forall k :: 0 <= k < qLen ==> dist[queue[k]] >= 0
      invariant dist[u] >= 0
      decreases n - j
    {
      if graph[u][j] && dist[j] == -1 && qLen < n {
        dist := dist[j := dist[u] + 1];
        queue[qLen] := j;
        qLen := qLen + 1;
      }
      j := j + 1;
    }
  }
}
