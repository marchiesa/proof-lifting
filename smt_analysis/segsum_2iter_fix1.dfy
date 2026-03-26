function segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// Two iterations, fix for iteration 1 only
method twoIterations(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i
  requires i + 2 <= |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+2])
{
  // Iteration 1
  var sum1 := sum + nums[i];
  assert nums[..i+1][..|nums[..i+1]|-1] == nums[..i];
  // Now Z3 knows: sum1 == segmentSum(nums[..i+1])

  // Iteration 2
  sum2 := sum1 + nums[i+1];
}
