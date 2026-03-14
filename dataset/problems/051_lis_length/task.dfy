// Longest Increasing Subsequence Length (DP)
// Task: Add loop invariants so that Dafny can verify this program.

ghost predicate IsSubsequence(sub: seq<int>, s: seq<int>)
{
  exists indices: seq<int> ::
    |indices| == |sub| &&
    (forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |s|) &&
    (forall i :: 0 <= i < |indices| ==> s[indices[i]] == sub[i]) &&
    (forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j])
}

predicate IsStrictlyIncreasing(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

method LISLength(a: seq<int>) returns (length: int)
  requires |a| > 0
  ensures length >= 1
  ensures length <= |a|
{
  // dp[i] = length of LIS ending at position i
  var dp := new int[|a|];
  var maxLen := 1;
  var i := 0;
  while i < |a|
  {
    dp[i] := 1;
    var j := 0;
    while j < i
    {
      if a[j] < a[i] && dp[j] + 1 > dp[i] {
        dp[i] := dp[j] + 1;
      }
      j := j + 1;
    }
    if dp[i] > maxLen {
      maxLen := dp[i];
    }
    i := i + 1;
  }
  length := maxLen;
}
