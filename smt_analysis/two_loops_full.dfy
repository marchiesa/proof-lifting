function {:fuel 2} segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

method twoLoopsUnrolled(nums: seq<int>) returns (total: int)
  requires |nums| == 2
  ensures total == segmentSum(nums) + segmentSum(nums)
{
  // === Loop 1: compute sum ===
  assert nums[..0] == [];
  assert segmentSum(nums[..0]) == 0;

  var sum := 0 + nums[0];
  assert nums[..1][..0] == nums[..0];

  sum := sum + nums[1];
  assert nums[..2][..1] == nums[..1];
  assert nums[..2] == nums;

  // === Loop 2: total = sum + each element again ===
  assert segmentSum(nums[..0]) == 0;

  total := sum + nums[0];
  assert nums[..1][..0] == nums[..0];

  total := total + nums[1];
  assert nums[..2][..1] == nums[..1];
  assert nums[..2] == nums;
}
