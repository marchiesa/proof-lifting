// Burst Balloons (DP)
// Task: Add loop invariants so that Dafny can verify this program.
// Find maximum coins by bursting all balloons.
// When balloon i is burst, earn nums[left]*nums[i]*nums[right].

function Max(a: int, b: int): int { if a >= b then a else b }

// Optimal score for bursting balloons in range (left, right) exclusive
function OptBurst(nums: seq<int>, left: int, right: int): int
  requires 0 <= left
  requires right <= |nums| - 1
  requires left <= right
  decreases right - left
{
  if left + 1 >= right then 0
  else
    MaxOverK(nums, left, right, left + 1)
}

function MaxOverK(nums: seq<int>, left: int, right: int, k: int): int
  requires 0 <= left
  requires right <= |nums| - 1
  requires left < right
  requires left < k <= right
  decreases right - left, right - k
{
  var score := nums[left] * nums[k] * nums[right] +
               OptBurst(nums, left, k) + OptBurst(nums, k, right);
  if k + 1 > right - 1 then score
  else Max(score, MaxOverK(nums, left, right, k + 1))
}

method BurstBalloons(a: seq<int>) returns (result: int)
  requires |a| >= 1
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures result >= 0
{
  // Pad with 1s on both sides
  var nums := [1] + a + [1];
  var n := |nums|;
  // dp[i][j] = OptBurst(nums, i, j)
  var dp := seq(n, i => seq(n, j => 0));
  var length := 2;
  while length < n
  {
    var left := 0;
    while left < n - length
    {
      var right := left + length;
      var k := left + 1;
      while k < right
      {
        var score := nums[left] * nums[k] * nums[right] + dp[left][k] + dp[k][right];
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
