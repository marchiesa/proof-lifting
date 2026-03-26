function segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// 4 asserts: 3 seq equalities + 1 sum checkpoint (after step 2 only)
// This tests whether 2 consecutive steps can work without an intermediate checkpoint
method sumThreeNumbers(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i
  requires i + 3 <= |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+3])
{
  sum2 := sum + nums[i];
  assert nums[..i+1][..|nums[..i+1]|-1] == nums[..i];
  // NO sum checkpoint here — can Z3 chain 2 steps with fuel 2?

  sum2 := sum2 + nums[i+1];
  assert nums[..i+2][..|nums[..i+2]|-1] == nums[..i+1];
  assert sum2 == segmentSum(nums[..i+2]);  // checkpoint resets fuel

  sum2 := sum2 + nums[i+2];
  assert nums[..i+3][..|nums[..i+3]|-1] == nums[..i+2];
}
