// Optimal Matrix Chain Multiplication (return min cost)
// Task: Add loop invariants so that Dafny can verify this program.

function Min(a: int, b: int): int { if a <= b then a else b }

// dims[i] x dims[i+1] are dimensions of matrix i
method MatrixChainOrder(dims: seq<int>) returns (result: int)
  requires |dims| >= 2
  requires forall i :: 0 <= i < |dims| ==> dims[i] > 0
  ensures result >= 0
{
  var n := |dims| - 1;
  if n == 1 { result := 0; return; }
  var dp := new int[n, n];

  var i := 0;
  while i < n { dp[i, i] := 0; i := i + 1; }

  // Initialize off-diagonal to 0
  i := 0;
  while i < n
  {
    var j := 0;
    while j < n
    {
      if j != i { dp[i, j] := 0; }
      j := j + 1;
    }
    i := i + 1;
  }

  var len := 2;
  while len <= n
  {
    i := 0;
    while i <= n - len
    {
      var j := i + len - 1;
      dp[i, j] := dp[i, i] + dp[i+1, j] + dims[i] * dims[i+1] * dims[j+1];
      var k := i + 1;
      while k < j
      {
        var cost := dp[i, k] + dp[k+1, j] + dims[i] * dims[k+1] * dims[j+1];
        dp[i, j] := Min(dp[i, j], cost);
        k := k + 1;
      }
      i := i + 1;
    }
    len := len + 1;
  }

  result := dp[0, n - 1];
}
