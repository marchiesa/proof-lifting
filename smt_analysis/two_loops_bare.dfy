function {:fuel 2} segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// Same two loops, NO manual assertions at all
method twoLoopsUnrolled(nums: seq<int>) returns (total: int)
  requires |nums| == 2
  ensures total == segmentSum(nums) + segmentSum(nums)
{
  // Loop 1
  var sum := 0 + nums[0];
  sum := sum + nums[1];

  // Loop 2
  total := sum + nums[0];
  total := total + nums[1];
}
