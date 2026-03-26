function segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// One iteration: we assume what holds BEFORE and try to prove what holds AFTER
// Pre:  sum == segmentSum(nums[..i]) and 0 <= i < |nums|
// Post: sum' == segmentSum(nums[..i+1])
// This is the inductive step — if we can prove this, we have the invariant.
method oneIteration(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i < |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+1])
{
  sum2 := sum + nums[i];
}
