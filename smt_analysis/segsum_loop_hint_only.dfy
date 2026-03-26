function segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// Full loop: invariant acts as checkpoint, trigger hint inside loop
method sumArray(nums: seq<int>) returns (sum: int)
  ensures sum == segmentSum(nums)
{
  sum := 0;
  var i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant sum == segmentSum(nums[..i])
  {
    sum := sum + nums[i];
    assert nums[..i+1][..i] == nums[..i];  // trigger hint only
    i := i + 1;
  }
  assert nums[..|nums|] == nums;  // post-loop hint
}
