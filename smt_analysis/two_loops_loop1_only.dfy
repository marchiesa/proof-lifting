function segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

method loop1Only(nums: seq<int>) returns (sum: int)
  requires |nums| == 2
  ensures sum == segmentSum(nums)
{
  sum := 0 + nums[0];
  assert nums[..1][..0] == nums[..0];

  sum := sum + nums[1];
  assert nums[..2][..1] == nums[..1];
  assert nums[..2] == nums;
}
