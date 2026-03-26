// Two loops:
// Loop 1: find the max
// Loop 2: compute (sum of nums) - |nums| * maxVal, prove it's <= 0
// Inter-loop fact: forall k :: 0 <= k < |nums| ==> nums[k] <= maxVal
//                  exists k :: 0 <= k < |nums| && nums[k] == maxVal

function sumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else sumSeq(s[..|s|-1]) + s[|s|-1]
}

method findMaxThenSum(nums: seq<int>) returns (maxVal: int, diff: int)
  requires |nums| > 0
  ensures forall k :: 0 <= k < |nums| ==> nums[k] <= maxVal
  ensures exists k :: 0 <= k < |nums| && nums[k] == maxVal
  ensures diff == sumSeq(nums) - |nums| * maxVal
  ensures diff <= 0
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

  // Loop 2: compute sum - |nums| * max
  diff := 0;
  var j := 0;
  while j < |nums|
    invariant 0 <= j <= |nums|
    invariant diff == sumSeq(nums[..j]) - j * maxVal
    invariant diff <= 0
  {
    assert nums[..j+1][..|nums[..j+1]|-1] == nums[..j];
    diff := diff + nums[j] - maxVal;
    j := j + 1;
  }
  assert nums[..|nums|] == nums;
}
