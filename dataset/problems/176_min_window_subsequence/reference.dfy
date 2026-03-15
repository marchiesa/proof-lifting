// Minimum Window Subsequence -- Reference solution with invariants

method MinWindowSubseq(a: seq<int>, b: seq<int>) returns (result: int)
  requires |a| > 0 && |b| > 0
  ensures result == -1 || result >= |b|
{
  var m := |a|; var n := |b|;
  var dp := new int[m + 1, n + 1];

  var i := 0;
  while i <= m
    invariant 0 <= i <= m + 1
    invariant forall r :: 0 <= r < i ==> dp[r, 0] == r
    invariant forall r, c :: 0 <= r < i && 1 <= c <= n ==> dp[r, c] == -1
    decreases m + 1 - i
  {
    dp[i, 0] := i;
    var j := 1;
    while j <= n
      invariant 1 <= j <= n + 1
      invariant dp[i, 0] == i
      invariant forall c :: 1 <= c < j ==> dp[i, c] == -1
      invariant forall r :: 0 <= r < i ==> dp[r, 0] == r
      invariant forall r, c :: 0 <= r < i && 1 <= c <= n ==> dp[r, c] == -1
      decreases n + 1 - j
    {
      dp[i, j] := -1;
      j := j + 1;
    }
    i := i + 1;
  }

  // Key property: dp[r, c] >= 0 ==> dp[r, c] <= r - c
  // (if b[0..c) is a subsequence of a[dp[r,c]..r), need at least c chars)
  i := 1;
  while i <= m
    invariant 1 <= i <= m + 1
    invariant forall r :: 0 <= r <= m ==> 0 <= dp[r, 0] <= r
    invariant forall r, c :: 0 <= r <= m && 1 <= c <= n ==> dp[r, c] >= -1
    invariant forall r, c :: 0 <= r <= m && 1 <= c <= n && dp[r, c] >= 0 ==> dp[r, c] <= r - c
    decreases m + 1 - i
  {
    var j := 1;
    while j <= n
      invariant 1 <= j <= n + 1
      invariant forall r :: 0 <= r <= m ==> 0 <= dp[r, 0] <= r
      invariant forall r, c :: 0 <= r <= m && 1 <= c <= n ==> dp[r, c] >= -1
      invariant forall r, c :: 0 <= r <= m && 1 <= c <= n && dp[r, c] >= 0 ==> dp[r, c] <= r - c
      decreases n + 1 - j
    {
      if a[i-1] == b[j-1] {
        dp[i, j] := dp[i-1, j-1];
      } else {
        dp[i, j] := dp[i-1, j];
      }
      j := j + 1;
    }
    i := i + 1;
  }

  result := -1;
  i := 1;
  while i <= m
    invariant 1 <= i <= m + 1
    invariant result == -1 || result >= n
    decreases m + 1 - i
  {
    if dp[i, n] != -1 {
      var windowLen := i - dp[i, n];
      assert dp[i, n] <= i - n;
      assert windowLen >= n;
      if result == -1 || windowLen < result {
        result := windowLen;
      }
    }
    i := i + 1;
  }
}
