// Matrix Chain Multiplication Order (DP)
// Task: Add loop invariants so that Dafny can verify this program.

method MatrixChain(dims: seq<nat>) returns (cost: nat)
  requires |dims| >= 2
  ensures true  // cost is the minimum multiplication cost
{
  var n := |dims| - 1; // number of matrices
  if n == 0 { return 0; }
  // dp[i][j] = min cost to multiply matrices i..j
  var dp := new nat[n, n];
  var i := 0;
  while i < n
  {
    dp[i, i] := 0;
    i := i + 1;
  }
  var length := 2;
  while length <= n
  {
    i := 0;
    while i <= n - length
    {
      var j := i + length - 1;
      dp[i, j] := 0xFFFF_FFFF;
      var k := i;
      while k < j
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
