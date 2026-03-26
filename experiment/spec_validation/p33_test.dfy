// Auxiliary predicate stating that a sequence is sorted in non-decreasing order
predicate isNonDecreasing(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// Post-condition predicate for searchRange
predicate searchRangePost(nums: seq<int>, target: int, result: seq<int>)
{
  |result| == 2 &&                                                                  // result must contain exactly two elements
  (
    (
      // Case 1: target not present in nums
      (forall k :: 0 <= k < |nums| ==> nums[k] != target) &&
      result[0] == -1 && 
      result[1] == -1
    )
    ||
    (
      // Case 2: target appears at least once in nums
      (exists k :: 0 <= k < |nums| && nums[k] == target) &&
      0 <= result[0] <= result[1] < |nums| &&                                      // indices are within bounds
      nums[result[0]] == target && 
      nums[result[1]] == target &&                                                 // boundary elements equal target
      (forall j :: 0 <= j < result[0] ==> nums[j] < target) &&                    // nothing equal to target before start
      (forall j :: result[1] < j < |nums| ==> nums[j] > target)                   // nothing equal to target after end
    )
  )
}

// method to be verified
method searchRange(nums: seq<int>, target: int) returns (result: seq<int>)
  requires isNonDecreasing(nums)                                                   // input array must be sorted
  ensures  searchRangePost(nums, target, result)                                   // must satisfy the post-condition predicate
{
    var start := -1;
    var end := -1;
    var left := 0;
    var right := |nums| - 1;
    
    while left <= right
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

method Main()
{
    var result;

    result := searchRange(nums:=[5, 7, 7, 8, 8, 10], target:=8);
    if result != [3, 4]
    {
        print("Test failed: with input (\"nums\":=[5, 7, 7, 8, 8, 10], \"target\":=8) got: ");
        print(result);
        print(" instead of \"[3, 4]\")\n");
    }

    result := searchRange(nums:=[5, 7, 7, 8, 8, 10], target:=6);
    if result != [-1, -1]
    {
        print("Test failed: with input (\"nums\":=[5, 7, 7, 8, 8, 10], \"target\":=6) got: ");
        print(result);
        print(" instead of \"[-1, -1]\")\n");
    }

    result := searchRange(nums:=[], target:=0);
    if result != [-1, -1]
    {
        print("Test failed: with input (\"nums\":=[], \"target\":=0) got: ");
        print(result);
        print(" instead of \"[-1, -1]\")\n");
    }

    result := searchRange(nums:=[1], target:=1);
    if result != [0, 0]
    {
        print("Test failed: with input (\"nums\":=[1], \"target\":=1) got: ");
        print(result);
        print(" instead of \"[0, 0]\")\n");
    }

    result := searchRange(nums:=[1, 1, 1, 1, 1], target:=1);
    if result != [0, 4]
    {
        print("Test failed: with input (\"nums\":=[1, 1, 1, 1, 1], \"target\":=1) got: ");
        print(result);
        print(" instead of \"[0, 4]\")\n");
    }

    result := searchRange(nums:=[1, 2, 3, 4, 5], target:=3);
    if result != [2, 2]
    {
        print("Test failed: with input (\"nums\":=[1, 2, 3, 4, 5], \"target\":=3) got: ");
        print(result);
        print(" instead of \"[2, 2]\")\n");
    }

    result := searchRange(nums:=[-10, -10, 0, 0, 0, 10, 10], target:=0);
    if result != [2, 4]
    {
        print("Test failed: with input (\"nums\":=[-10, -10, 0, 0, 0, 10, 10], \"target\":=0) got: ");
        print(result);
        print(" instead of \"[2, 4]\")\n");
    }

    result := searchRange(nums:=[-109, 0, 109], target:=109);
    if result != [2, 2]
    {
        print("Test failed: with input (\"nums\":=[-109, 0, 109], \"target\":=109) got: ");
        print(result);
        print(" instead of \"[2, 2]\")\n");
    }

}
