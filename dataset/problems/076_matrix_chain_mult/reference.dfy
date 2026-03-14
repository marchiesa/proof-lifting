// Matrix Chain Multiplication Order (DP) -- Reference solution with invariants

method MatrixChain(dims: seq<nat>) returns (cost: nat)
  requires |dims| >= 2
  ensures true  // cost is the minimum multiplication cost
{
  var n := |dims| - 1;
  if n == 0 { return 0; }
  var dp := new nat[n, n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    dp[i, i] := 0;
    i := i + 1;
  }
  var length := 2;
  while length <= n
    invariant 2 <= length <= n + 1
    decreases n + 1 - length
  {
    i := 0;
    while i <= n - length
      invariant 0 <= i <= n - length + 1
      decreases n - length - i + 1
    {
      var j := i + length - 1;
      dp[i, j] := 0xFFFF_FFFF;
      var k := i;
      while k < j
        invariant i <= k <= j
        decreases j - k
      {
        var q := dp[i, k] + dp[k + 1, j] + dims[i] * dims[k + 1] * dims[j + 1];
        if q < dp[i, j] {
          dp[i, j] := q;
        }
        k := k + 1;
      }
      i := i + 1;
    }
    length := length + 1;
  }
  cost := dp[0, n - 1];
}
