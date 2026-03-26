predicate isNonDecreasing(a: seq<int>)
  reads {}
{
  forall i:int, j:int :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate rotatedSorted(nums: seq<int>)
  reads {}
{
  |nums| > 0 &&
  (exists k:int ::
      0 <= k < |nums| &&
      isNonDecreasing(nums[k..] + nums[..k]))
}

predicate searchPost(nums: seq<int>, target: int, found: bool)
  reads {}
{
  found <==> (exists i:int :: 0 <= i < |nums| && nums[i] == target)
}

// method to be verified
method search(nums: seq<int>, target: int) returns (found: bool)
  requires rotatedSorted(nums)
  ensures  searchPost(nums, target, found)
{
    var left := 0;
    var right := |nums| - 1;
    
    while left <= right
    {
        var mid := left + (right - left) / 2;
        
        if nums[mid] == target
        {
            return true;
        }
        
        if nums[mid] == nums[left]
        {
            left := left + 1;
        }
        else if nums[mid] > nums[left]
        {
            if nums[left] <= target && target < nums[mid]
            {
                right := mid - 1;
            }
            else
            {
                left := mid + 1;
            }
        }
        else
        {
            if nums[mid] < target && target <= nums[right]
            {
                left := mid + 1;
            }
            else
            {
                right := mid - 1;
            }
        }
    }
    
    return false;
}

method Main()
{
    var result;

    result := search(nums:=[2, 5, 6, 0, 0, 1, 2], target:=0);
    if result != True
    {
        print("Test failed: with input (\"nums\":=[2, 5, 6, 0, 0, 1, 2], \"target\":=0) got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := search(nums:=[2, 5, 6, 0, 0, 1, 2], target:=3);
    if result != False
    {
        print("Test failed: with input (\"nums\":=[2, 5, 6, 0, 0, 1, 2], \"target\":=3) got: ");
        print(result);
        print(" instead of \"False\")\n");
    }

    result := search(nums:=[1], target:=1);
    if result != True
    {
        print("Test failed: with input (\"nums\":=[1], \"target\":=1) got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := search(nums:=[1], target:=0);
    if result != False
    {
        print("Test failed: with input (\"nums\":=[1], \"target\":=0) got: ");
        print(result);
        print(" instead of \"False\")\n");
    }

    result := search(nums:=[1, 1, 1, 1, 1, 1, 1], target:=1);
    if result != True
    {
        print("Test failed: with input (\"nums\":=[1, 1, 1, 1, 1, 1, 1], \"target\":=1) got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := search(nums:=[1, 1, 1, 1, 1, 1, 1], target:=2);
    if result != False
    {
        print("Test failed: with input (\"nums\":=[1, 1, 1, 1, 1, 1, 1], \"target\":=2) got: ");
        print(result);
        print(" instead of \"False\")\n");
    }

    result := search(nums:=[2, 2, 2, 3, 2, 2, 2], target:=3);
    if result != True
    {
        print("Test failed: with input (\"nums\":=[2, 2, 2, 3, 2, 2, 2], \"target\":=3) got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := search(nums:=[4, 5, 6, 7, 0, 1, 2], target:=0);
    if result != True
    {
        print("Test failed: with input (\"nums\":=[4, 5, 6, 7, 0, 1, 2], \"target\":=0) got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := search(nums:=[4, 5, 6, 7, 0, 1, 2], target:=3);
    if result != False
    {
        print("Test failed: with input (\"nums\":=[4, 5, 6, 7, 0, 1, 2], \"target\":=3) got: ");
        print(result);
        print(" instead of \"False\")\n");
    }

}
