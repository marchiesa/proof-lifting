// Auxiliary function: does the given sequence contain the value v?
function SeqContains(s: seq<int>, v: int): bool
{
  exists i:int :: 0 <= i < |s| && s[i] == v
}

// Post-condition for firstMissingPositive
predicate firstMissingPositivePost(nums: seq<int>, result: int)
{
  // result is the smallest strictly-positive integer
  // that does not appear in nums
  result > 0
  && !SeqContains(nums, result)
  && (forall x:int :: 1 <= x < result ==> SeqContains(nums, x))
}


// method to be verified
method firstMissingPositive(nums: seq<int>) returns (result: int)
  requires |nums| >= 1                       // 1 ≤ nums.length
  ensures  firstMissingPositivePost(nums, result)
{
    var n := |nums|;
    var arr := new int[n];
    var i := 0;
    
    // Copy sequence to array for in-place modification
    while i < n {
        arr[i] := nums[i];
        i := i + 1;
    }
    
    i := 0;
    while i < n {
        // While current number is in valid range and not in correct position
        while 1 <= arr[i] <= n && arr[arr[i] - 1] != arr[i] {
            // Swap numbers
            var temp := arr[arr[i] - 1];
            arr[arr[i] - 1] := arr[i];
            arr[i] := temp;
        }
        i := i + 1;
    }
    
    i := 0;
    while i < n {
        if arr[i] != i + 1 {
            return i + 1;
        }
        i := i + 1;
    }
    
    return n + 1;
}

method Main()
{
    var result;

    result := firstMissingPositive(nums:=[1, 2, 0]);
    if result != 3
    {
        print("Test failed: with input (\"nums\":=[1, 2, 0]) got: ");
        print(result);
        print(" instead of \"3\")\n");
    }

    result := firstMissingPositive(nums:=[3, 4, -1, 1]);
    if result != 2
    {
        print("Test failed: with input (\"nums\":=[3, 4, -1, 1]) got: ");
        print(result);
        print(" instead of \"2\")\n");
    }

    result := firstMissingPositive(nums:=[7, 8, 9, 11, 12]);
    if result != 1
    {
        print("Test failed: with input (\"nums\":=[7, 8, 9, 11, 12]) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := firstMissingPositive(nums:=[1]);
    if result != 2
    {
        print("Test failed: with input (\"nums\":=[1]) got: ");
        print(result);
        print(" instead of \"2\")\n");
    }

    result := firstMissingPositive(nums:=[2]);
    if result != 1
    {
        print("Test failed: with input (\"nums\":=[2]) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := firstMissingPositive(nums:=[-1, -2, -3]);
    if result != 1
    {
        print("Test failed: with input (\"nums\":=[-1, -2, -3]) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := firstMissingPositive(nums:=[1, 1, 1, 1]);
    if result != 2
    {
        print("Test failed: with input (\"nums\":=[1, 1, 1, 1]) got: ");
        print(result);
        print(" instead of \"2\")\n");
    }

    result := firstMissingPositive(nums:=[1, 2, 3, 4, 5]);
    if result != 6
    {
        print("Test failed: with input (\"nums\":=[1, 2, 3, 4, 5]) got: ");
        print(result);
        print(" instead of \"6\")\n");
    }

    result := firstMissingPositive(nums:=[0, 0, 0, 0]);
    if result != 1
    {
        print("Test failed: with input (\"nums\":=[0, 0, 0, 0]) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := firstMissingPositive(nums:=[2147483647, 2147483646, 2147483645]);
    if result != 1
    {
        print("Test failed: with input (\"nums\":=[2147483647, 2147483646, 2147483645]) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := firstMissingPositive(nums:=[-2147483648, -2147483647, -2147483646]);
    if result != 1
    {
        print("Test failed: with input (\"nums\":=[-2147483648, -2147483647, -2147483646]) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

}
