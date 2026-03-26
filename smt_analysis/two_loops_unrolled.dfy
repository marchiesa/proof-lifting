function segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// Two sequential loops, unrolled for |nums| == 2:
// Loop 1: sum = sum of nums
// Loop 2: total = sum + sum of nums again = 2 * sum of nums
method twoLoopsUnrolled(nums: seq<int>) returns (total: int)
  requires |nums| == 2
  ensures total == 2 * segmentSum(nums)
{
  // === Loop 1: compute sum ===
  // Iteration 1
  var sum := 0 + nums[0];
  assert nums[..1][..0] == nums[..0];

  // Iteration 2
  sum := sum + nums[1];
  assert nums[..2][..1] == nums[..1];
  assert nums[..2] == nums;

  // === Loop 2: add each element to sum again ===
  // Iteration 1
  total := sum + nums[0];
  assert nums[..1][..0] == nums[..0];

  // Iteration 2
  total := total + nums[1];
  assert nums[..2][..1] == nums[..1];
  assert nums[..2] == nums;
}
