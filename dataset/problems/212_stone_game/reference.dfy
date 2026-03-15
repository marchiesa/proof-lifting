// Stone Game -- Reference solution with invariants

function Max(a: int, b: int): int { if a >= b then a else b }

function OptimalScore(piles: seq<int>, i: int, j: int): int
  requires 0 <= i <= j < |piles|
  decreases j - i
{
  if i == j then piles[i]
  else Max(piles[i] - OptimalScore(piles, i+1, j),
           piles[j] - OptimalScore(piles, i, j-1))
}

method StoneGame(piles: seq<int>) returns (diff: int)
  requires |piles| > 0
  requires forall i :: 0 <= i < |piles| ==> piles[i] > 0
  ensures diff == OptimalScore(piles, 0, |piles| - 1)
{
  var n := |piles|;
  var dp := seq(n * n, _ => 0);

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |dp| == n * n
    invariant forall k :: 0 <= k < i ==> dp[k * n + k] == piles[k]
    decreases n - i
  {
    dp := dp[..i * n + i] + [piles[i]] + dp[i * n + i + 1..];
    i := i + 1;
  }

  var length := 2;
  while length <= n
    invariant 2 <= length <= n + 1
    invariant |dp| == n * n
    decreases n + 1 - length
  {
    i := 0;
    while i + length - 1 < n
      invariant 0 <= i
      invariant |dp| == n * n
      decreases n - length + 1 - i
    {
      var j := i + length - 1;
      var pickLeft := piles[i] - dp[(i+1) * n + j];
      var pickRight := piles[j] - dp[i * n + (j-1)];
      var val := Max(pickLeft, pickRight);
      dp := dp[..i * n + j] + [val] + dp[i * n + j + 1..];
      i := i + 1;
    }
    length := length + 1;
  }
  diff := dp[0 * n + (n - 1)];
}
