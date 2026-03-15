// Shortest Common Supersequence -- Reference solution with invariants

function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

method LCSLength(a: seq<int>, b: seq<int>) returns (lcsLen: int)
  ensures 0 <= lcsLen <= Min(|a|, |b|)
{
  var m := |a|;
  var n := |b|;
  var dp := new int[m + 1, n + 1];

  var i := 0;
  while i <= m
    invariant 0 <= i <= m + 1
    invariant forall k :: 0 <= k < i ==> dp[k, 0] == 0
    decreases m + 1 - i
  {
    dp[i, 0] := 0;
    i := i + 1;
  }
  var j := 0;
  while j <= n
    invariant 0 <= j <= n + 1
    invariant forall k :: 0 <= k <= m ==> dp[k, 0] == 0
    invariant forall k :: 0 <= k < j ==> dp[0, k] == 0
    decreases n + 1 - j
  {
    dp[0, j] := 0;
    j := j + 1;
  }

  i := 1;
  while i <= m
    invariant 1 <= i <= m + 1
    invariant forall k :: 0 <= k <= m ==> dp[k, 0] == 0
    invariant forall k :: 0 <= k <= n ==> dp[0, k] == 0
    invariant forall r, c :: 1 <= r < i && 0 <= c <= n ==> 0 <= dp[r, c] <= Min(r, c)
    decreases m + 1 - i
  {
    j := 1;
    while j <= n
      invariant 1 <= j <= n + 1
      invariant forall k :: 0 <= k <= m ==> dp[k, 0] == 0
      invariant forall k :: 0 <= k <= n ==> dp[0, k] == 0
      invariant forall c :: 1 <= c < j ==> 0 <= dp[i, c] <= Min(i, c)
      invariant forall r, c :: 1 <= r < i && 0 <= c <= n ==> 0 <= dp[r, c] <= Min(r, c)
      decreases n + 1 - j
    {
      if a[i-1] == b[j-1] {
        dp[i, j] := dp[i-1, j-1] + 1;
      } else {
        dp[i, j] := Max(dp[i-1, j], dp[i, j-1]);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  lcsLen := dp[m, n];
}

method ShortestCommonSuperseqLen(a: seq<int>, b: seq<int>) returns (result: int)
  ensures result >= Max(|a|, |b|)
{
  var lcs := LCSLength(a, b);
  result := |a| + |b| - lcs;
}
