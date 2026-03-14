// Tarjan's Bridges Finding -- Reference solution with invariants

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
    invariant 0 <= i <= n
    invariant |disc| == n && |low| == n
    invariant forall k :: 0 <= k < |bridges| ==> 0 <= bridges[k].0 < n && 0 <= bridges[k].1 < n
    decreases n - i
  {
    if disc[i] == -1 {
      var stackN: seq<int> := [i];
      var stackP: seq<int> := [-1];
      var stackJ: seq<int> := [0];
      disc := disc[i := timer];
      low := low[i := timer];
      timer := timer + 1;
      var fuel := n * n;
      while |stackN| > 0 && fuel > 0
        invariant |disc| == n && |low| == n
        invariant |stackN| == |stackP| == |stackJ|
        invariant forall k :: 0 <= k < |stackN| ==> 0 <= stackN[k] < n
        invariant forall k :: 0 <= k < |stackJ| ==> 0 <= stackJ[k]
        invariant forall k :: 0 <= k < |bridges| ==> 0 <= bridges[k].0 < n && 0 <= bridges[k].1 < n
        decreases fuel
      {
        var u := stackN[|stackN| - 1];
        var par := stackP[|stackP| - 1];
        var j := stackJ[|stackJ| - 1];
        if j >= n {
          stackN := stackN[..|stackN| - 1];
          stackP := stackP[..|stackP| - 1];
          stackJ := stackJ[..|stackJ| - 1];
          if |stackN| > 0 {
            var pU := stackN[|stackN| - 1];
            if low[u] < low[pU] {
              low := low[pU := low[u]];
            }
            if low[u] > disc[pU] {
              bridges := bridges + [(pU, u)];
            }
          }
        } else {
          stackJ := stackJ[..|stackJ| - 1] + [j + 1];
          if graph[u][j] && j != par {
            if disc[j] == -1 {
              disc := disc[j := timer];
              low := low[j := timer];
              timer := timer + 1;
              stackN := stackN + [j];
              stackP := stackP + [u];
              stackJ := stackJ + [0];
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
