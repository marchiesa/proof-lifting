// Articulation Points Finding -- Reference solution with invariants

method FindArticulationPoints(graph: seq<seq<bool>>, n: int) returns (isAP: seq<bool>)
  requires n >= 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  requires forall i, j :: 0 <= i < n && 0 <= j < n ==> graph[i][j] == graph[j][i]
  ensures |isAP| == n
{
  var disc := seq(n, _ => -1);
  var low := seq(n, _ => -1);
  isAP := seq(n, _ => false);
  var timer := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |disc| == n && |low| == n && |isAP| == n
    decreases n - i
  {
    if disc[i] == -1 {
      var stackN: seq<int> := [i];
      var stackP: seq<int> := [-1];
      var stackJ: seq<int> := [0];
      var childCount := seq(n, _ => 0);
      disc := disc[i := timer];
      low := low[i := timer];
      timer := timer + 1;
      var fuel := n * n;
      while |stackN| > 0 && fuel > 0
        invariant |disc| == n && |low| == n && |isAP| == n && |childCount| == n
        invariant |stackN| == |stackP| == |stackJ|
        invariant forall k :: 0 <= k < |stackN| ==> 0 <= stackN[k] < n
        invariant forall k :: 0 <= k < |stackJ| ==> 0 <= stackJ[k]
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
            if low[u] < low[pU] { low := low[pU := low[u]]; }
            if par != -1 && low[u] >= disc[pU] { isAP := isAP[pU := true]; }
            childCount := childCount[pU := childCount[pU] + 1];
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
      if childCount[i] > 1 {
        isAP := isAP[i := true];
      }
    }
    i := i + 1;
  }
}
