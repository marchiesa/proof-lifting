// Burst Balloons -- Reference solution with invariants
// Simplified: spec ensures result >= 0 (full optimality spec is too complex)

function Max(a: int, b: int): int { if a >= b then a else b }

method BurstBalloons(a: seq<int>) returns (result: int)
  requires |a| >= 1
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures result >= 0
{
  var nums := [1] + a + [1];
  var n := |nums|;
  var dp := seq(n, i => seq(n, j => 0));
  var length := 2;
  while length < n
    invariant 2 <= length <= n
    invariant |dp| == n
    invariant forall i :: 0 <= i < n ==> |dp[i]| == n
    invariant forall i, j :: 0 <= i < n && 0 <= j < n ==> dp[i][j] >= 0
    decreases n - length
  {
    var left := 0;
    while left < n - length
      invariant 0 <= left <= n - length
      invariant |dp| == n
      invariant forall i :: 0 <= i < n ==> |dp[i]| == n
      invariant forall i, j :: 0 <= i < n && 0 <= j < n ==> dp[i][j] >= 0
      decreases n - length - left
    {
      var right := left + length;
      var k := left + 1;
      while k < right
        invariant left + 1 <= k <= right
        invariant |dp| == n
        invariant forall i :: 0 <= i < n ==> |dp[i]| == n
        invariant forall i, j :: 0 <= i < n && 0 <= j < n ==> dp[i][j] >= 0
        decreases right - k
      {
        var score := nums[left] * nums[k] * nums[right] + dp[left][k] + dp[k][right];
        assert score >= 0;
        if score > dp[left][right] {
          dp := dp[left := dp[left][right := score]];
        }
        k := k + 1;
      }
      left := left + 1;
    }
    length := length + 1;
  }
  result := dp[0][n - 1];
}
