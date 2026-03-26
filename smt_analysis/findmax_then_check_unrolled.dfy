function {:fuel 3} sumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else sumSeq(s[..|s|-1]) + s[|s|-1]
}

// Unrolled for |nums| == 3, no invariants, no hints
method findMaxThenSum(nums: seq<int>) returns (maxVal: int, diff: int)
  requires |nums| == 3
  ensures forall k :: 0 <= k < |nums| ==> nums[k] <= maxVal
  ensures exists k :: 0 <= k < |nums| && nums[k] == maxVal
  ensures diff == sumSeq(nums) - |nums| * maxVal
  ensures diff <= 0
{
  // Loop 1: find max (unrolled)
  maxVal := nums[0];
  if nums[1] > maxVal { maxVal := nums[1]; }
  if nums[2] > maxVal { maxVal := nums[2]; }

  // Loop 2: compute diff (unrolled)
  diff := 0;
  diff := diff + nums[0] - maxVal;
  diff := diff + nums[1] - maxVal;
  diff := diff + nums[2] - maxVal;
}
