function segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// One iteration with the discovered fix
method oneIteration(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i < |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+1])
{
  sum2 := sum + nums[i];
  // Fix: tell Z3 that taking i elements from nums[..i+1] gives nums[..i]
  assert nums[..i+1][..|nums[..i+1]|-1] == nums[..i];
}
