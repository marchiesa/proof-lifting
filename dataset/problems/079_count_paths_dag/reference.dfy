// Count Paths in DAG -- Reference solution with invariants

method CountPaths(graph: seq<seq<bool>>, n: int, src: int, tgt: int) returns (count: nat)
  requires n > 0
  requires 0 <= src < n && 0 <= tgt < n
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  ensures count >= 0
{
  var dp := seq(n, _ => 0);
  dp := dp[tgt := 1];
  var iter := 0;
  while iter < n
    invariant 0 <= iter <= n
    invariant |dp| == n
    invariant forall i :: 0 <= i < n ==> dp[i] >= 0
    decreases n - iter
  {
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |dp| == n
      invariant forall i :: 0 <= i < n ==> dp[i] >= 0
      decreases n - i
    {
      if i != tgt {
        var sum := 0;
        var j := 0;
        while j < n
          invariant 0 <= j <= n
          invariant sum >= 0
          decreases n - j
        {
          if graph[i][j] {
            sum := sum + dp[j];
          }
          j := j + 1;
        }
        dp := dp[i := sum];
      }
      i := i + 1;
    }
    iter := iter + 1;
  }
  count := dp[src];
}
