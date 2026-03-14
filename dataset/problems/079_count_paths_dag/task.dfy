// Count Paths in DAG
// Task: Add loop invariants so that Dafny can verify this program.

method CountPaths(graph: seq<seq<bool>>, n: int, src: int, tgt: int) returns (count: nat)
  requires n > 0
  requires 0 <= src < n && 0 <= tgt < n
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  ensures count >= 0
{
  // dp[i] = number of paths from i to tgt
  var dp := seq(n, _ => 0);
  dp := dp[tgt := 1];

  // Process in reverse topological order (simplified: iterate n times)
  var iter := 0;
  while iter < n
  {
    var i := 0;
    while i < n
    {
      if i != tgt {
        var sum := 0;
        var j := 0;
        while j < n
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
