// Maximum Sum Increasing Subsequence -- Reference solution with invariants

function Max(a: int, b: int): int { if a >= b then a else b }

method MaxSumIncreasingSubseq(a: seq<int>) returns (result: int)
  requires |a| > 0
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures result >= 0
{
  var n := |a|;
  var dp := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> dp[k] >= 0
    decreases n - i
  {
    dp[i] := a[i];
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant dp[i] >= a[i] >= 0
      invariant forall k :: 0 <= k < i ==> dp[k] >= 0
      decreases i - j
    {
      if a[j] < a[i] {
        dp[i] := Max(dp[i], dp[j] + a[i]);
      }
      j := j + 1;
    }
    i := i + 1;
  }

  result := dp[0];
  i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant result >= 0
    decreases n - i
  {
    result := Max(result, dp[i]);
    i := i + 1;
  }
}
