// Minimum Path Sum in Grid -- Reference solution with invariants

function Min(a: int, b: int): int { if a <= b then a else b }

method MinPathSum(grid: seq<seq<int>>) returns (result: int)
  requires |grid| > 0
  requires |grid[0]| > 0
  requires forall i :: 0 <= i < |grid| ==> |grid[i]| == |grid[0]|
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] >= 0
  ensures result >= 0
{
  var m := |grid|;
  var n := |grid[0]|;
  var dp := new int[m, n];

  dp[0, 0] := grid[0][0];
  var j := 1;
  while j < n
    invariant 1 <= j <= n
    invariant forall k :: 0 <= k < j ==> dp[0, k] >= 0
    decreases n - j
  {
    dp[0, j] := dp[0, j-1] + grid[0][j];
    j := j + 1;
  }

  var i := 1;
  while i < m
    invariant 1 <= i <= m
    invariant forall r, c :: 0 <= r < i && 0 <= c < n ==> dp[r, c] >= 0
    decreases m - i
  {
    dp[i, 0] := dp[i-1, 0] + grid[i][0];
    j := 1;
    while j < n
      invariant 1 <= j <= n
      invariant dp[i, 0] >= 0
      invariant forall c :: 0 <= c < j ==> dp[i, c] >= 0
      invariant forall r, c :: 0 <= r < i && 0 <= c < n ==> dp[r, c] >= 0
      decreases n - j
    {
      dp[i, j] := Min(dp[i-1, j], dp[i, j-1]) + grid[i][j];
      j := j + 1;
    }
    i := i + 1;
  }

  result := dp[m-1, n-1];
}
