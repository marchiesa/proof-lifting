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

    // Loop 1: find leftmost occurrence of target
    while left <= right
      invariant 0 <= left <= |nums|
      invariant -1 <= right <= |nums| - 1
      invariant left <= right + 1
      invariant forall k :: 0 <= k < left ==> nums[k] < target
      invariant start == -1 ==> (forall k :: right < k < |nums| ==> nums[k] > target)
      invariant start != -1 ==> (0 <= start < |nums| && nums[start] == target)
      invariant start != -1 ==> right < start
      invariant start != -1 ==> (forall k :: start < k < |nums| ==> nums[k] >= target)
      invariant start != -1 ==> (forall k :: right < k < start ==> nums[k] != target)
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

    // After loop 1: establish properties of start
    assert left == right + 1;
    if start == -1 {
      assert forall k :: 0 <= k < |nums| ==> nums[k] != target;
    } else {
      assert left <= start;
      assert forall k :: 0 <= k < left ==> nums[k] < target;
      assert forall k :: right < k < start ==> nums[k] != target;
      assert forall k :: 0 <= k < start ==> nums[k] < target;
    }

    ghost var startFinal := start;
    assert startFinal == -1 ==> (forall k :: 0 <= k < |nums| ==> nums[k] != target);
    assert startFinal != -1 ==> (0 <= startFinal < |nums| && nums[startFinal] == target);
    assert startFinal != -1 ==> (forall k :: 0 <= k < startFinal ==> nums[k] < target);

    left := 0;
    right := |nums| - 1;

    // Loop 2: find rightmost occurrence of target
    while left <= right
      invariant 0 <= left <= |nums|
      invariant -1 <= right <= |nums| - 1
      invariant left <= right + 1
      invariant forall k :: right < k < |nums| ==> nums[k] > target
      invariant end == -1 ==> (forall k :: 0 <= k < left ==> nums[k] < target)
      invariant end != -1 ==> (0 <= end < |nums| && nums[end] == target)
      invariant end != -1 ==> end < left
      invariant end != -1 ==> (forall k :: end < k < left ==> nums[k] != target)
      invariant start == startFinal
      invariant startFinal == -1 ==> end == -1
      invariant startFinal == -1 ==> (forall k :: 0 <= k < |nums| ==> nums[k] != target)
      invariant startFinal != -1 ==> (0 <= startFinal < |nums| && nums[startFinal] == target)
      invariant startFinal != -1 ==> (forall k :: 0 <= k < startFinal ==> nums[k] < target)
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

    // After loop 2: establish properties of end
    assert left == right + 1;
    if end == -1 {
      assert forall k :: 0 <= k < |nums| ==> nums[k] != target;
      assert startFinal == -1;
      assert start == -1;
    } else {
      assert forall k :: end < k < left ==> nums[k] != target;
      assert forall k :: right < k < |nums| ==> nums[k] > target;
      assert forall k :: end < k < |nums| ==> nums[k] > target;
      assert startFinal != -1;
    }

    result := [start, end];
}
