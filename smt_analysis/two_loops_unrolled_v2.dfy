function segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// Postcondition: total = segmentSum(nums) + segmentSum(nums)
method twoLoopsUnrolled(nums: seq<int>) returns (total: int)
  requires |nums| == 2
  ensures total == segmentSum(nums) + segmentSum(nums)
{
  // === Loop 1: compute sum ===
  var sum := 0 + nums[0];
  assert nums[..1][..0] == nums[..0];

  sum := sum + nums[1];
  assert nums[..2][..1] == nums[..1];
  assert nums[..2] == nums;
  // Now: sum == segmentSum(nums)

  // === Loop 2: total = sum + each element again ===
  total := sum + nums[0];
  assert nums[..1][..0] == nums[..0];

  total := total + nums[1];
  assert nums[..2][..1] == nums[..1];
  assert nums[..2] == nums;
  // Now: total == sum + segmentSum(nums) == 2 * segmentSum(nums)
}
