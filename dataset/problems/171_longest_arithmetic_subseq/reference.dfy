// Longest Arithmetic Subsequence -- Reference solution with invariants

function Max(a: int, b: int): int { if a >= b then a else b }

method LongestArithSubseq(a: seq<int>) returns (result: int)
  requires |a| >= 2
  ensures result >= 2
{
  var n := |a|;
  var dp := new map<int, int>[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    dp[i] := map[];
    i := i + 1;
  }

  result := 2;
  i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant result >= 2
    decreases n - i
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant result >= 2
      decreases i - j
    {
      var diff := a[i] - a[j];
      var prevLen := if diff in dp[j] then dp[j][diff] else 1;
      var newLen := prevLen + 1;
      var curLen := if diff in dp[i] then dp[i][diff] else 0;
      if newLen > curLen {
        dp[i] := dp[i][diff := newLen];
      }
      result := Max(result, newLen);
      j := j + 1;
    }
    i := i + 1;
  }
}
