function segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// Only intermediate sum asserts, no sequence equality asserts
method sumThreeNumbers(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i
  requires i + 3 <= |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+3])
{
  sum2 := sum + nums[i];
  assert sum2 == segmentSum(nums[..i+1]);

  sum2 := sum2 + nums[i+1];
  assert sum2 == segmentSum(nums[..i+2]);

  sum2 := sum2 + nums[i+2];
}
