predicate isNonDecreasing(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate searchRangePost(nums: seq<int>, target: int, result: seq<int>)
{
  |result| == 2 &&
  (
    (
      (forall k :: 0 <= k < |nums| ==> nums[k] != target) &&
      result[0] == -1 &&
      result[1] == -1
    )
    ||
    (
      (exists k :: 0 <= k < |nums| && nums[k] == target) &&
      0 <= result[0] <= result[1] < |nums| &&
      nums[result[0]] == target &&
      nums[result[1]] == target &&
      (forall j :: 0 <= j < result[0] ==> nums[j] < target) &&
      (forall j :: result[1] < j < |nums| ==> nums[j] > target)
    )
  )
}

method searchRange(nums: seq<int>, target: int) returns (result: seq<int>)
  requires isNonDecreasing(nums)
  ensures  searchRangePost(nums, target, result)
{
    var start := -1;
    var end := -1;
    var left := 0;
    var right := |nums| - 1;

    while left <= right
      invariant 0 <= left <= |nums|
      invariant -1 <= right <= |nums| - 1
      invariant left <= right + 1
      invariant forall k :: 0 <= k < left ==> nums[k] < target
      invariant forall k :: right < k < |nums| ==> nums[k] >= target
      invariant start == -1 ==> forall k :: right < k < |nums| ==> nums[k] > target
      invariant start != -1 ==> 0 <= start < |nums| && nums[start] == target
      invariant start != -1 ==> start == right + 1
    {
        var mid := left + (right - left) / 2;
        if nums[mid] < target
        {
            left := mid + 1;
        }
        else
        {
            right := mid - 1;
            if nums[mid] == target
            {
                start := mid;
            }
        }
    }

    left := 0;
    right := |nums| - 1;

    while left <= right
      invariant 0 <= left <= |nums|
      invariant -1 <= right <= |nums| - 1
      invariant left <= right + 1
      invariant forall k :: 0 <= k < left ==> nums[k] <= target
      invariant forall k :: right < k < |nums| ==> nums[k] > target
      invariant end == -1 ==> forall k :: 0 <= k < left ==> nums[k] < target
      invariant end != -1 ==> 0 <= end < |nums| && nums[end] == target
      invariant end != -1 ==> end == left - 1
    {
        var mid := left + (right - left) / 2;
        if nums[mid] > target
        {
            right := mid - 1;
        }
        else
        {
            left := mid + 1;
            if nums[mid] == target
            {
                end := mid;
            }
        }
    }

    result := [start, end];
}
