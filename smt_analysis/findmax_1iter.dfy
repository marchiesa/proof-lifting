// Single iteration: symbolic i, symbolic maxVal
method findMaxStep(nums: seq<int>, i: int, maxVal: int) returns (maxVal2: int)
  requires |nums| > 0
  requires 1 <= i < |nums|
  requires exists k :: 0 <= k < i && nums[k] == maxVal
  requires forall k :: 0 <= k < i ==> nums[k] <= maxVal
  ensures exists k :: 0 <= k < i + 1 && nums[k] == maxVal2
  ensures forall k :: 0 <= k < i + 1 ==> nums[k] <= maxVal2
{
  if nums[i] > maxVal {
    maxVal2 := nums[i];
  } else {
    maxVal2 := maxVal;
  }
}
