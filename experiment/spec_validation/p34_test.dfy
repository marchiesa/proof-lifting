predicate StrictSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

predicate searchInsertPost(nums: seq<int>, target: int, index: int)
{
  // index is a valid position in, or just after, the array
  0 <= index <= |nums|

  // every element before index is strictly smaller than target
  && (forall k :: 0 <= k < index ==> nums[k] < target)

  // every element after index is strictly greater than target
  && (forall k :: index < k < |nums| ==> target < nums[k])

  // if target occurs in nums, index points exactly to that occurrence
  && ((exists k :: 0 <= k < |nums| && nums[k] == target)
        ==> (index < |nums| && nums[index] == target))
}

// method to be verified
method searchInsert(nums: seq<int>, target: int) returns (index: int)
  requires |nums| >= 1
  requires StrictSorted(nums)
  ensures  searchInsertPost(nums, target, index)
{
    var left := 0;
    var right := |nums| - 1;
    
    while left <= right
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

method Main()
{
    var result;

    result := searchInsert(nums:=[1, 3, 5, 6], target:=5);
    if result != 2
    {
        print("Test failed: with input (\"nums\":=[1, 3, 5, 6], \"target\":=5) got: ");
        print(result);
        print(" instead of \"2\")\n");
    }

    result := searchInsert(nums:=[1, 3, 5, 6], target:=2);
    if result != 1
    {
        print("Test failed: with input (\"nums\":=[1, 3, 5, 6], \"target\":=2) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := searchInsert(nums:=[1, 3, 5, 6], target:=7);
    if result != 4
    {
        print("Test failed: with input (\"nums\":=[1, 3, 5, 6], \"target\":=7) got: ");
        print(result);
        print(" instead of \"4\")\n");
    }

    result := searchInsert(nums:=[1], target:=0);
    if result != 0
    {
        print("Test failed: with input (\"nums\":=[1], \"target\":=0) got: ");
        print(result);
        print(" instead of \"0\")\n");
    }

    result := searchInsert(nums:=[1], target:=2);
    if result != 1
    {
        print("Test failed: with input (\"nums\":=[1], \"target\":=2) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := searchInsert(nums:=[1, 3], target:=2);
    if result != 1
    {
        print("Test failed: with input (\"nums\":=[1, 3], \"target\":=2) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := searchInsert(nums:=[-3, -1, 3, 90], target:=0);
    if result != 2
    {
        print("Test failed: with input (\"nums\":=[-3, -1, 3, 90], \"target\":=0) got: ");
        print(result);
        print(" instead of \"2\")\n");
    }

    result := searchInsert(nums:=[1, 3, 5, 6], target:=1);
    if result != 0
    {
        print("Test failed: with input (\"nums\":=[1, 3, 5, 6], \"target\":=1) got: ");
        print(result);
        print(" instead of \"0\")\n");
    }

    result := searchInsert(nums:=[1, 3, 5, 6], target:=6);
    if result != 3
    {
        print("Test failed: with input (\"nums\":=[1, 3, 5, 6], \"target\":=6) got: ");
        print(result);
        print(" instead of \"3\")\n");
    }

    result := searchInsert(nums:=[-104, 0, 104], target:=-105);
    if result != 0
    {
        print("Test failed: with input (\"nums\":=[-104, 0, 104], \"target\":=-105) got: ");
        print(result);
        print(" instead of \"0\")\n");
    }

    result := searchInsert(nums:=[-104, 0, 104], target:=105);
    if result != 3
    {
        print("Test failed: with input (\"nums\":=[-104, 0, 104], \"target\":=105) got: ");
        print(result);
        print(" instead of \"3\")\n");
    }

}
