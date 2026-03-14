// Longest Common Subsequence (DP)
// Task: Add loop invariants so that Dafny can verify this program.

// Recursive spec for LCS length
function LCSLen(a: seq<int>, b: seq<int>): nat
  decreases |a|, |b|
{
  if |a| == 0 || |b| == 0 then 0
  else if a[|a|-1] == b[|b|-1] then 1 + LCSLen(a[..|a|-1], b[..|b|-1])
  else Max(LCSLen(a[..|a|-1], b), LCSLen(a, b[..|b|-1]))
}

function Max(x: int, y: int): int { if x >= y then x else y }

method ComputeLCS(a: seq<int>, b: seq<int>) returns (result: nat)
  ensures result == LCSLen(a, b)
{
  var m := |a|;
  var n := |b|;
  // dp[i][j] = LCSLen(a[..i], b[..j])
  var dp := new int[m + 1, n + 1];
  var i := 0;
  while i <= m
  {
    dp[i, 0] := 0;
    i := i + 1;
  }
  var j := 0;
  while j <= n
  {
    dp[0, j] := 0;
    j := j + 1;
  }
  i := 1;
  while i <= m
  {
    j := 1;
    while j <= n
    {
      if a[i-1] == b[j-1] {
        dp[i, j] := dp[i-1, j-1] + 1;
      } else {
        dp[i, j] := Max(dp[i-1, j], dp[i, j-1]);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := dp[m, n];
}
