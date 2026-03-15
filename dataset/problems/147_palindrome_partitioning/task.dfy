// Palindrome Partitioning (Minimum Cuts)
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsPalindromeRange(s: seq<char>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |s|
{
  forall i {:trigger s[lo + i]} :: 0 <= i < (hi - lo) / 2 ==> s[lo + i] == s[hi - 1 - i]
}

method MinPalindromeCuts(s: seq<char>) returns (cuts: int)
  ensures cuts >= 0
  ensures |s| <= 1 ==> cuts == 0
{
  if |s| <= 1 {
    return 0;
  }
  var n := |s|;
  var dp := new int[n];
  var i := 0;
  while i < n
  {
    dp[i] := i; // worst case: cut at each position
    var j := 0;
    while j <= i
    {
      if IsPalindromeRange(s, j, i + 1) {
        var candidate := if j == 0 then 0 else dp[j - 1] + 1;
        if candidate < dp[i] {
          dp[i] := candidate;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
  cuts := dp[n - 1];
}
