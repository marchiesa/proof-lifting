// Unique Paths in Grid (DP)
// Task: Add loop invariants so that Dafny can verify this program.

function Paths(m: nat, n: nat): nat
  decreases m + n
{
  if m == 0 || n == 0 then 0
  else if m == 1 || n == 1 then 1
  else Paths(m - 1, n) + Paths(m, n - 1)
}

method UniquePaths(m: nat, n: nat) returns (result: nat)
  requires m > 0 && n > 0
  ensures result == Paths(m, n)
{
  // Use DP: 1D array of size n
  var dp := seq(n, i => 1);
  var i := 1;
  while i < m
  {
    var j := 1;
    while j < n
    {
      dp := dp[..j] + [dp[j] + dp[j-1]] + dp[j+1..];
      j := j + 1;
    }
    i := i + 1;
  }
  result := dp[n - 1];
}
