// Palindrome Partitioning -- Reference solution with invariants

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
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> dp[k] >= 0 && dp[k] <= k
    decreases n - i
  {
    dp[i] := i;
    var j := 0;
    while j <= i
      invariant 0 <= j <= i + 1
      invariant dp[i] >= 0
      invariant dp[i] <= i
      invariant forall k :: 0 <= k < i ==> dp[k] >= 0 && dp[k] <= k
      decreases i + 1 - j
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
