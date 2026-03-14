// Palindrome Partitioning: Minimum Cuts -- Reference solution with invariants

predicate IsPalindrome(s: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |s|
{
  forall i :: 0 <= i < (hi - lo) / 2 ==> s[lo + i] == s[hi - 1 - i]
}

method PalindromeMinCuts(s: seq<int>) returns (result: int)
  requires |s| > 0
  ensures 0 <= result <= |s| - 1
  ensures IsPalindrome(s, 0, |s|) ==> result == 0
{
  var n := |s|;
  var dp := seq(n + 1, k requires 0 <= k <= n => if k <= 1 then 0 else k - 1);
  var i := 2;
  while i <= n
    invariant 2 <= i <= n + 1
    invariant |dp| == n + 1
    invariant dp[0] == 0 && dp[1] == 0
    invariant forall k :: 0 <= k < i ==> 0 <= dp[k] <= (if k == 0 then 0 else k - 1)
    invariant forall k :: 0 <= k < i && IsPalindrome(s, 0, k) ==> dp[k] == 0
    invariant forall k :: i <= k <= n ==> dp[k] == k - 1
    decreases n + 1 - i
  {
    var best := i - 1;
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant 0 <= best <= i - 1
      invariant j > 0 && IsPalindrome(s, 0, i) ==> best == 0
      decreases i - j
    {
      if IsPalindrome(s, j, i) {
        var cost := if j == 0 then 0 else dp[j] + 1;
        if cost < best {
          best := cost;
        }
      }
      j := j + 1;
    }
    dp := dp[i := best];
    i := i + 1;
  }
  result := dp[n];
}
