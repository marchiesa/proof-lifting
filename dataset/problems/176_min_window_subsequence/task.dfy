// Minimum Window Subsequence (DP)
// Task: Add loop invariants so that Dafny can verify this program.

// Given sequences a and b, find the length of the minimum window in a
// that contains b as a subsequence. Returns -1 if no such window exists.

method MinWindowSubseq(a: seq<int>, b: seq<int>) returns (result: int)
  requires |a| > 0 && |b| > 0
  ensures result == -1 || result >= |b|
{
  var m := |a|; var n := |b|;
  // dp[i][j] = starting index of minimum window in a[..i] containing b[..j]
  // -1 means no such window
  var dp := new int[m + 1, n + 1];

  var i := 0;
  while i <= m
  {
    dp[i, 0] := i; // empty b matched trivially at position i
    var j := 1;
    while j <= n
    {
      dp[i, j] := -1;
      j := j + 1;
    }
    i := i + 1;
  }

  i := 1;
  while i <= m
  {
    var j := 1;
    while j <= n
    {
      if a[i-1] == b[j-1] {
        dp[i, j] := dp[i-1, j-1];
      } else {
        dp[i, j] := dp[i-1, j];
      }
      j := j + 1;
    }
    i := i + 1;
  }

  result := -1;
  i := 1;
  while i <= m
  {
    if dp[i, n] != -1 {
      var windowLen := i - dp[i, n];
      if result == -1 || windowLen < result {
        result := windowLen;
      }
    }
    i := i + 1;
  }
}
