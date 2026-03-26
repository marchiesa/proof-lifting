function segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// Two iterations unrolled, no invariant, no hints
method twoIterations(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i
  requires i + 2 <= |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+2])
{
  // Iteration 1
  var sum1 := sum + nums[i];

  // Iteration 2
  sum2 := sum1 + nums[i+1];
}
