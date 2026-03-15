// Longest Arithmetic Subsequence (DP)
// Task: Add loop invariants so that Dafny can verify this program.

function Max(a: int, b: int): int { if a >= b then a else b }

method LongestArithSubseq(a: seq<int>) returns (result: int)
  requires |a| >= 2
  ensures result >= 2
{
  var n := |a|;
  // dp[i] maps difference -> length of arithmetic subseq ending at i
  var dp := new map<int, int>[n];
  var i := 0;
  while i < n
  {
    dp[i] := map[];
    i := i + 1;
  }

  result := 2;
  i := 1;
  while i < n
  {
    var j := 0;
    while j < i
    {
      var diff := a[i] - a[j];
      var prevLen := if diff in dp[j] then dp[j][diff] else 1;
      var newLen := prevLen + 1;
      dp[i] := if diff in dp[i] then
        (if dp[i][diff] >= newLen then dp[i] else dp[i][diff := newLen])
        else dp[i][diff := newLen];
      result := Max(result, newLen);
      j := j + 1;
    }
    i := i + 1;
  }
}
