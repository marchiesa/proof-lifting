function segmentSum(nums: seq<int>, start: int, end: int): int
  requires 0 <= start <= end <= |nums|
  decreases end - start
{
  if start == end
  then 0
  else nums[start] + segmentSum(nums, start + 1, end)
}

predicate maxSubArrayPost(nums: seq<int>, maxSum: int)
  reads {}
{
  // A sub-array whose sum is maxSum exists
  (exists s:int, e:int ::
      0 <= s < e <= |nums| &&
      segmentSum(nums, s, e) == maxSum) &&

  // No sub-array has a larger sum
  (forall i:int, j:int ::
      0 <= i < j <= |nums| ==> segmentSum(nums, i, j) <= maxSum)
}

// method to be verified
method maxSubArray(nums: seq<int>) returns (maxSum: int)
  requires |nums| >= 1
  ensures  maxSubArrayPost(nums, maxSum)
{
    var currentSum := nums[0];
    maxSum := nums[0];
    
    var i := 1;
    while i < |nums|
    {
        if currentSum + nums[i] > nums[i] {
            currentSum := currentSum + nums[i];
        } else {
            currentSum := nums[i];
        }
        
        if currentSum > maxSum {
            maxSum := currentSum;
        }
        
        i := i + 1;
    }
}

method Main()
{
    var result;

    result := maxSubArray(nums:=[-2, 1, -3, 4, -1, 2, 1, -5, 4]);
    if result != 6
    {
        print("Test failed: with input (\"nums\":=[-2, 1, -3, 4, -1, 2, 1, -5, 4]) got: ");
        print(result);
        print(" instead of \"6\")\n");
    }

    result := maxSubArray(nums:=[1]);
    if result != 1
    {
        print("Test failed: with input (\"nums\":=[1]) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := maxSubArray(nums:=[5, 4, -1, 7, 8]);
    if result != 23
    {
        print("Test failed: with input (\"nums\":=[5, 4, -1, 7, 8]) got: ");
        print(result);
        print(" instead of \"23\")\n");
    }

    result := maxSubArray(nums:=[-1]);
    if result != -1
    {
        print("Test failed: with input (\"nums\":=[-1]) got: ");
        print(result);
        print(" instead of \"-1\")\n");
    }

    result := maxSubArray(nums:=[-1, -2, -3]);
    if result != -1
    {
        print("Test failed: with input (\"nums\":=[-1, -2, -3]) got: ");
        print(result);
        print(" instead of \"-1\")\n");
    }

    result := maxSubArray(nums:=[0, 0, 0, 0]);
    if result != 0
    {
        print("Test failed: with input (\"nums\":=[0, 0, 0, 0]) got: ");
        print(result);
        print(" instead of \"0\")\n");
    }

    result := maxSubArray(nums:=[-5, 1, 2, 3, -2, 4, -1]);
    if result != 8
    {
        print("Test failed: with input (\"nums\":=[-5, 1, 2, 3, -2, 4, -1]) got: ");
        print(result);
        print(" instead of \"8\")\n");
    }

    result := maxSubArray(nums:=[1, 2, 3, 4, 5]);
    if result != 15
    {
        print("Test failed: with input (\"nums\":=[1, 2, 3, 4, 5]) got: ");
        print(result);
        print(" instead of \"15\")\n");
    }

    result := maxSubArray(nums:=[-10000]);
    if result != -10000
    {
        print("Test failed: with input (\"nums\":=[-10000]) got: ");
        print(result);
        print(" instead of \"-10000\")\n");
    }

    result := maxSubArray(nums:=[10000]);
    if result != 10000
    {
        print("Test failed: with input (\"nums\":=[10000]) got: ");
        print(result);
        print(" instead of \"10000\")\n");
    }

}
