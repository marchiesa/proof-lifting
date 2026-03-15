// Count Palindromic Subsequences (DP)
// Task: Add loop invariants so that Dafny can verify this program.

// Count total palindromic subsequences in a sequence.

method CountPalindromicSubseq(s: seq<int>) returns (result: int)
  requires |s| > 0
  ensures result >= 1
{
  var n := |s|;
  var dp := new int[n, n];

  // Init: zero out everything first
  var i := 0;
  while i < n
  {
    var j := 0;
    while j < n
    {
      dp[i, j] := 0;
      j := j + 1;
    }
    i := i + 1;
  }

  // Each single character is a palindrome
  i := 0;
  while i < n
  {
    dp[i, i] := 1;
    i := i + 1;
  }

  var gap := 1;
  while gap < n
  {
    i := 0;
    while i + gap < n
    {
      var j := i + gap;
      if s[i] == s[j] {
        dp[i, j] := dp[i+1, j] + dp[i, j-1] + 1;
      } else {
        dp[i, j] := dp[i+1, j] + dp[i, j-1] - dp[i+1, j-1];
      }
      i := i + 1;
    }
    gap := gap + 1;
  }

  result := dp[0, n - 1];
}
