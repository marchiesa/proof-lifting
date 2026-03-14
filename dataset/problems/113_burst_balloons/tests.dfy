// Burst Balloons -- Runtime spec tests

function Max(a: int, b: int): int { if a >= b then a else b }

// Iterative version of OptBurst for testing
// dp[left][right] = optimal score for bursting balloons in (left, right) exclusive
method ComputeOptBurst(nums: seq<int>) returns (dp: seq<seq<int>>)
  requires |nums| >= 3
  requires forall i :: 0 <= i < |nums| ==> nums[i] >= 0
  ensures |dp| == |nums|
  ensures forall i :: 0 <= i < |dp| ==> |dp[i]| == |nums|
{
  var n := |nums|;
  dp := seq(n, i => seq(n, j => 0));
  var length := 2;
  while length < n
    invariant 2 <= length <= n
    invariant |dp| == n
    invariant forall i :: 0 <= i < n ==> |dp[i]| == n
  {
    var left := 0;
    while left < n - length
      invariant 0 <= left <= n - length
      invariant |dp| == n
      invariant forall i :: 0 <= i < n ==> |dp[i]| == n
    {
      var right := left + length;
      var k := left + 1;
      while k < right
        invariant left + 1 <= k <= right
        invariant |dp| == n
        invariant forall i :: 0 <= i < n ==> |dp[i]| == n
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
}

method Main()
{
  // Test burst of single balloon: [5] -> padded to [1,5,1]
  // OptBurst([1,5,1], 0, 2) = 1*5*1 = 5
  var dp1 := ComputeOptBurst([1, 5, 1]);
  expect dp1[0][2] == 5, "Burst [5] = 1*5*1 = 5";

  // Test burst of [3, 1]: padded to [1, 3, 1, 1]
  // Best: burst 1 first (3*1*1=3), then burst 3 (1*3*1=3): total 6
  // Or: burst 3 first (1*3*1=3), then burst 1 (1*1*1=1): total 4
  // Max = 6
  var dp2 := ComputeOptBurst([1, 3, 1, 1]);
  expect dp2[0][3] == 6, "Burst [3,1] = 6";

  // Test burst of [3, 1, 5]: padded to [1, 3, 1, 5, 1]
  var dp3 := ComputeOptBurst([1, 3, 1, 5, 1]);
  expect dp3[0][4] >= 0, "Burst [3,1,5] should be non-negative";
  // k=1: 1*3*1 + dp[0][1] + dp[1][4]; k=2: 1*1*1 + dp[0][2] + dp[2][4]; k=3: 1*5*1 + dp[0][3] + dp[3][4]
  // dp[1][4]: k=2: 3*1*1 + dp[1][2] + dp[2][4] = 3 + 0 + dp[2][4]
  //   dp[2][4]: k=3: 1*5*1 = 5; dp[2][4] = 5
  //   dp[1][4]: k=2: 3+0+5=8; k=3: 3*5*1=15+0+0=15; Max(8,15) = 15
  // dp[0][4] k=1: 1*3*1 + 0 + 15 = 18
  // dp[0][2]: k=1: 1*3*1 = 3
  // dp[0][4] k=2: 1*1*1 + 3 + 5 = 9
  // dp[0][3]: k=1: 1*3*1 + 0 + dp[1][3]; dp[1][3]: k=2: 3*1*5=15; dp[1][3]=15; dp[0][3] k=1: 3+0+15=18
  //   dp[0][3] k=2: 1*1*5 + dp[0][2] + dp[2][3] = 5+3+0 = 8; max(18,8) = 18
  // dp[0][4] k=3: 1*5*1 + 18 + 0 = 23
  // Max(18, 9, 23) = 23
  expect dp3[0][4] == 35, "Burst [3,1,5] optimally = 35";

  // Negative tests
  expect dp1[0][2] != 0, "Burst [5] should not be 0";
  expect dp2[0][3] != 4, "Burst [3,1] should not be 4";

  // Single no-op
  expect dp1[0][1] == 0, "OptBurst with adjacent = 0";

  print "All spec tests passed\n";
}
