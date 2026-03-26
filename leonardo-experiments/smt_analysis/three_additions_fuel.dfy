function segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// Use {:fuel segmentSum, 4} to allow 4 unfoldings instead of default 2
method sumThreeNumbers(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i
  requires i + 3 <= |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+3])
{
  // 3 seq equality asserts only, no sum checkpoint — relying on extra fuel
  sum2 := sum + nums[i];
  assert {:fuel segmentSum, 4} nums[..i+1][..|nums[..i+1]|-1] == nums[..i];

  sum2 := sum2 + nums[i+1];
  assert {:fuel segmentSum, 4} nums[..i+2][..|nums[..i+2]|-1] == nums[..i+1];

  sum2 := sum2 + nums[i+2];
  assert {:fuel segmentSum, 4} nums[..i+3][..|nums[..i+3]|-1] == nums[..i+2];
}
