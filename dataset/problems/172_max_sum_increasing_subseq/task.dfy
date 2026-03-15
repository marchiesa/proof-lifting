// Maximum Sum Increasing Subsequence (DP)
// Task: Add loop invariants so that Dafny can verify this program.

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
  {
    dp[i] := a[i];
    var j := 0;
    while j < i
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
  {
    result := Max(result, dp[i]);
    i := i + 1;
  }
}
