// Edit Distance (Dynamic Programming) -- Reference solution with invariants

function Min3(a: int, b: int, c: int): int
{
  if a <= b && a <= c then a
  else if b <= c then b
  else c
}

method EditDistance(s: seq<int>, t: seq<int>) returns (dist: int)
  ensures dist >= 0
  ensures dist <= |s| + |t|
{
  var m := |s|;
  var n := |t|;
  var dp := new int[m + 1, n + 1];

  var i := 0;
  while i <= m
    invariant 0 <= i <= m + 1
    invariant forall k :: 0 <= k < i ==> dp[k, 0] == k
    decreases m + 1 - i
  {
    dp[i, 0] := i;
    i := i + 1;
  }

  var j := 0;
  while j <= n
    invariant 0 <= j <= n + 1
    invariant forall k :: 0 <= k < j ==> dp[0, k] == k
    invariant forall k :: 0 <= k <= m ==> dp[k, 0] == k
    decreases n + 1 - j
  {
    dp[0, j] := j;
    j := j + 1;
  }

  i := 1;
  while i <= m
    invariant 1 <= i <= m + 1
    invariant forall k :: 0 <= k <= m ==> dp[k, 0] == k
    invariant forall k :: 0 <= k <= n ==> dp[0, k] == k
    invariant forall a, b :: 0 <= a < i && 0 <= b <= n ==> dp[a, b] >= 0 && dp[a, b] <= a + b
    invariant forall b :: 0 <= b <= n ==> dp[i-1, b] >= 0 && dp[i-1, b] <= (i-1) + b
    decreases m + 1 - i
  {
    j := 1;
    while j <= n
      invariant 1 <= j <= n + 1
      invariant forall k :: 0 <= k <= m ==> dp[k, 0] == k
      invariant forall k :: 0 <= k <= n ==> dp[0, k] == k
      invariant forall a, b :: 0 <= a < i && 0 <= b <= n ==> dp[a, b] >= 0 && dp[a, b] <= a + b
      invariant forall b :: 0 <= b < j ==> dp[i, b] >= 0 && dp[i, b] <= i + b
      invariant forall b :: j <= b <= n ==> dp[i-1, b] >= 0 && dp[i-1, b] <= (i-1) + b
      decreases n + 1 - j
    {
      if s[i - 1] == t[j - 1] {
        dp[i, j] := dp[i - 1, j - 1];
      } else {
        dp[i, j] := 1 + Min3(dp[i - 1, j], dp[i, j - 1], dp[i - 1, j - 1]);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  dist := dp[m, n];
}
