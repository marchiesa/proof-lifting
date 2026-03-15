// Minimum Path Sum in Grid (DP)
// Task: Add loop invariants so that Dafny can verify this program.

function Min(a: int, b: int): int { if a <= b then a else b }

// grid is represented as seq<seq<int>> with uniform row length
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
  {
    dp[0, j] := dp[0, j-1] + grid[0][j];
    j := j + 1;
  }

  var i := 1;
  while i < m
  {
    dp[i, 0] := dp[i-1, 0] + grid[i][0];
    j := 1;
    while j < n
    {
      dp[i, j] := Min(dp[i-1, j], dp[i, j-1]) + grid[i][j];
      j := j + 1;
    }
    i := i + 1;
  }

  result := dp[m-1, n-1];
}
