// Reference: full program with invariants
method findMaxAndCount(nums: seq<int>) returns (maxVal: int, count: int)
  requires |nums| > 0
  ensures forall k :: 0 <= k < |nums| ==> nums[k] <= maxVal
  ensures exists k :: 0 <= k < |nums| && nums[k] == maxVal
  ensures count >= 1
  ensures count == |set k | 0 <= k < |nums| && nums[k] == maxVal|
{
  // Loop 1: find max
  maxVal := nums[0];
  var i := 1;
  while i < |nums|
    invariant 1 <= i <= |nums|
    invariant forall k :: 0 <= k < i ==> nums[k] <= maxVal
    invariant exists k :: 0 <= k < i && nums[k] == maxVal
  {
    if nums[i] > maxVal {
      maxVal := nums[i];
    }
    i := i + 1;
  }

  // Loop 2: count occurrences of max
  count := 0;
  var j := 0;
  while j < |nums|
    invariant 0 <= j <= |nums|
    invariant count == |set k | 0 <= k < j && nums[k] == maxVal|
  {
    if nums[j] == maxVal {
      count := count + 1;
      assert (set k | 0 <= k < j + 1 && nums[k] == maxVal)
           == (set k | 0 <= k < j && nums[k] == maxVal) + {j};
    } else {
      assert (set k | 0 <= k < j + 1 && nums[k] == maxVal)
           == (set k | 0 <= k < j && nums[k] == maxVal);
    }
    j := j + 1;
  }

  // count >= 1 because exists k :: nums[k] == maxVal
  assert maxVal in (set k | 0 <= k < |nums| && nums[k] == maxVal);
}
