function {:fuel 3} segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// Three iterations, no checkpoints, just more fuel
method threeIterations(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i
  requires i + 3 <= |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+3])
{
  // Iteration 1
  var sum1 := sum + nums[i];
  assert nums[..i+1][..i] == nums[..i];

  // Iteration 2
  var sum12 := sum1 + nums[i+1];
  assert nums[..i+2][..i+1] == nums[..i+1];

  // Iteration 3
  sum2 := sum12 + nums[i+2];
  assert nums[..i+3][..i+2] == nums[..i+2];
}
