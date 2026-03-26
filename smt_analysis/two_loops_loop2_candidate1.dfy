function {:fuel 2} segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// Candidate: sum == segmentSum(nums)
method loop2Alone(nums: seq<int>, sum: int) returns (total: int)
  requires |nums| == 2
  requires sum == segmentSum(nums)
  ensures total == segmentSum(nums) + segmentSum(nums)
{
  total := sum + nums[0];
  total := total + nums[1];
}
