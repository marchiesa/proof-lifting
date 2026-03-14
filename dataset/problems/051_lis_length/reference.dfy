// Longest Increasing Subsequence Length (DP) -- Reference solution with invariants

method LISLength(a: seq<int>) returns (length: int)
  requires |a| > 0
  ensures length >= 1
  ensures length <= |a|
{
  var dp := new int[|a|];
  var maxLen := 1;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant 1 <= maxLen
    invariant maxLen <= |a|
    invariant forall k :: 0 <= k < i ==> 1 <= dp[k] <= k + 1
    invariant forall k :: 0 <= k < i ==> dp[k] <= maxLen
    decreases |a| - i
  {
    dp[i] := 1;
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant 1 <= dp[i]
      invariant dp[i] <= j + 1
      invariant forall k :: 0 <= k < i ==> 1 <= dp[k] <= k + 1
      invariant forall k :: 0 <= k < i ==> dp[k] <= maxLen
      decreases i - j
    {
      if a[j] < a[i] && dp[j] + 1 > dp[i] {
        dp[i] := dp[j] + 1;
      }
      j := j + 1;
    }
    assert 1 <= dp[i] <= i + 1;
    if dp[i] > maxLen {
      maxLen := dp[i];
    }
    i := i + 1;
  }
  length := maxLen;
}
