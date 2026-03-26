predicate StrictSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

predicate searchInsertPost(nums: seq<int>, target: int, index: int)
{
  0 <= index <= |nums|
  && (forall k :: 0 <= k < index ==> nums[k] < target)
  && (forall k :: index < k < |nums| ==> target < nums[k])
  && ((exists k :: 0 <= k < |nums| && nums[k] == target)
        ==> (index < |nums| && nums[index] == target))
}

method searchInsert(nums: seq<int>, target: int) returns (index: int)
  requires |nums| >= 1
  requires StrictSorted(nums)
  ensures  searchInsertPost(nums, target, index)
{
    var left := 0;
    var right := |nums| - 1;

    while left <= right
      invariant 0 <= left <= |nums|
      invariant -1 <= right <= |nums| - 1
      invariant forall k :: 0 <= k < left ==> nums[k] < target
      invariant forall k :: right < k < |nums| ==> target < nums[k]
      invariant forall k :: 0 <= k < |nums| && nums[k] == target ==> left <= k <= right
    {
        var mid := left + (right - left) / 2;

        if nums[mid] == target {
            return mid;
        }

        if nums[mid] < target {
            left := mid + 1;
        } else {
            right := mid - 1;
        }
    }

    return left;
}
