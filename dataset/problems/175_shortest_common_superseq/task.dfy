// Shortest Common Supersequence (DP)
// Task: Add loop invariants so that Dafny can verify this program.

function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

// Length of LCS
method LCSLength(a: seq<int>, b: seq<int>) returns (lcsLen: int)
  ensures 0 <= lcsLen <= Min(|a|, |b|)
{
  var m := |a|;
  var n := |b|;
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
  lcsLen := dp[m, n];
}

// SCS length = |a| + |b| - LCS(a, b)
method ShortestCommonSuperseqLen(a: seq<int>, b: seq<int>) returns (result: int)
  ensures result >= Max(|a|, |b|)
{
  var lcs := LCSLength(a, b);
  result := |a| + |b| - lcs;
}
