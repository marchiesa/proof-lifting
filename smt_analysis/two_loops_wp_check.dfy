function {:fuel 2} segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// Check: is the WP equivalent to sum == segmentSum(nums)?
// WP is: sum + nums[0] + nums[1] == 2 * segmentSum(nums)
// We check both directions.

lemma wpEquivalence(nums: seq<int>, sum: int)
  requires |nums| == 2
  ensures (sum + nums[0] + nums[1] == 2 * segmentSum(nums))
      <==> (sum == segmentSum(nums))
{
}
