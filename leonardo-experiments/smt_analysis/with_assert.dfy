function segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

method sumOneNumberToArray(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i < |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+1])
{
  sum2 := sum + nums[i];
  assert nums[..i+1][..|nums[..i+1]|-1] == nums[..i];
  return sum2;
}
