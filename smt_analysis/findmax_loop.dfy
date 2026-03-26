// Reference: the full loop with invariants
method findMax(nums: seq<int>) returns (maxVal: int)
  requires |nums| > 0
  ensures exists k :: 0 <= k < |nums| && nums[k] == maxVal
  ensures forall k :: 0 <= k < |nums| ==> nums[k] <= maxVal
{
  maxVal := nums[0];
  var i := 1;
  while i < |nums|
    invariant 1 <= i <= |nums|
    invariant exists k :: 0 <= k < i && nums[k] == maxVal
    invariant forall k :: 0 <= k < i ==> nums[k] <= maxVal
  {
    if nums[i] > maxVal {
      maxVal := nums[i];
    }
    i := i + 1;
  }
}
