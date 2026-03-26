// Unrolled for |nums| == 3, no invariants, no hints
method findMax(nums: seq<int>) returns (maxVal: int)
  requires |nums| == 3
  ensures exists k :: 0 <= k < |nums| && nums[k] == maxVal
  ensures forall k :: 0 <= k < |nums| ==> nums[k] <= maxVal
{
  // Iteration 0: init
  maxVal := nums[0];

  // Iteration 1
  if nums[1] > maxVal {
    maxVal := nums[1];
  }

  // Iteration 2
  if nums[2] > maxVal {
    maxVal := nums[2];
  }
}
