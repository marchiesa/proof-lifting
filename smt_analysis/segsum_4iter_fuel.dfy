function {:fuel 4} segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// Four iterations, no checkpoints, fuel=4
method fourIterations(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i
  requires i + 4 <= |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+4])
{
  var sum1 := sum + nums[i];
  assert nums[..i+1][..i] == nums[..i];

  var sum12 := sum1 + nums[i+1];
  assert nums[..i+2][..i+1] == nums[..i+1];

  var sum13 := sum12 + nums[i+2];
  assert nums[..i+3][..i+2] == nums[..i+2];

  sum2 := sum13 + nums[i+3];
  assert nums[..i+4][..i+3] == nums[..i+3];
}
