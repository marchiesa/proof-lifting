function {:fuel 1} sumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else sumSeq(s[..|s|-1]) + s[|s|-1]
}

// Loop 2 alone, 1 iteration, symbolic size.
// maxVal is a free parameter — what precondition does it need?
method loop2Step(nums: seq<int>, j: int, maxVal: int, diff: int)
    returns (diff2: int)
  requires |nums| > 0
  requires 0 <= j < |nums|
  requires diff == sumSeq(nums[..j]) - j * maxVal
  requires diff <= 0
  ensures diff2 == sumSeq(nums[..j+1]) - (j+1) * maxVal
  ensures diff2 <= 0
{
  assert nums[..j+1][..|nums[..j+1]|-1] == nums[..j];
  diff2 := diff + nums[j] - maxVal;
}
