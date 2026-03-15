// Minimum Insertions to Make Palindrome (DP)
// Task: Add loop invariants so that Dafny can verify this program.

// Find minimum number of insertions to make a sequence a palindrome.
// Uses LPS (Longest Palindromic Subsequence) approach: answer = n - LPS.

function Max(a: int, b: int): int { if a >= b then a else b }

method MinInsertionsPalindrome(s: seq<int>) returns (result: int)
  requires |s| > 0
  ensures 0 <= result < |s|
{
  var n := |s|;
  // dp[i][j] = length of longest palindromic subsequence of s[i..j]
  var dp := new int[n, n];

  // Init all to 0
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

  // Set diagonal: LPS of single element = 1
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
        dp[i, j] := dp[i+1, j-1] + 2;
      } else {
        dp[i, j] := Max(dp[i+1, j], dp[i, j-1]);
      }
      i := i + 1;
    }
    gap := gap + 1;
  }

  // min insertions = n - LPS length
  result := n - dp[0, n - 1];
}
