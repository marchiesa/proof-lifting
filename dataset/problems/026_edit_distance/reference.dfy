// Edit Distance (Levenshtein Distance) -- Reference solution with invariants

function Min3(a: int, b: int, c: int): int
{
  if a <= b && a <= c then a
  else if b <= c then b
  else c
}

lemma Min3Bound(a: int, b: int, c: int)
  ensures Min3(a, b, c) <= a
  ensures Min3(a, b, c) <= b
  ensures Min3(a, b, c) <= c
  ensures Min3(a, b, c) >= 0 ==> (a >= 0 || b >= 0 || c >= 0)
{}

method EditDistance(a: seq<int>, b: seq<int>) returns (dist: int)
  ensures dist >= 0
  ensures dist <= |a| + |b|
{
  var m := |a|;
  var n := |b|;

  // dp[i] represents edit distance from a[0..i] to b[0..j] (column by column)
  // We use a 1D array with rolling updates
  var prev := seq(n + 1, j => j);
  var i := 0;

  while i < m
    invariant 0 <= i <= m
    invariant |prev| == n + 1
    invariant forall j :: 0 <= j <= n ==> prev[j] >= 0
    invariant forall j :: 0 <= j <= n ==> prev[j] <= i + j
    decreases m - i
  {
    var curr := [i + 1] + seq(n, _ => 0);
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |curr| == n + 1
      invariant |prev| == n + 1
      invariant forall k :: 0 <= k <= j ==> curr[k] >= 0
      invariant forall k :: 0 <= k <= j ==> curr[k] <= i + 1 + k
      invariant forall k :: 0 <= k <= n ==> prev[k] >= 0
      invariant forall k :: 0 <= k <= n ==> prev[k] <= i + k
      decreases n - j
    {
      if a[i] == b[j] {
        curr := curr[j + 1 := prev[j]];
      } else {
        var minVal := Min3(prev[j], prev[j + 1], curr[j]);
        assert minVal >= 0;
        assert minVal <= prev[j] <= i + j;
        curr := curr[j + 1 := 1 + minVal];
      }
      j := j + 1;
    }
    prev := curr;
    i := i + 1;
  }
  dist := prev[n];
}
