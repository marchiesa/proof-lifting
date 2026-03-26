predicate twoSumPost(nums: seq<int>, target: int, result: seq<int>)
  reads {}
{
  |result| == 2
  && 0 <= result[0] < |nums|
  && 0 <= result[1] < |nums|
  && result[0] != result[1]
  && nums[result[0]] + nums[result[1]] == target
}

// method to be verified
method twoSum(nums: seq<int>, target: int) returns (result: seq<int>)
  requires |nums| >= 2
  requires exists i, j :: 0 <= i < |nums| && 0 <= j < |nums| && i != j && nums[i] + nums[j] == target
  ensures  twoSumPost(nums, target, result)
{
    var hashTable := map[];
    var i := 0;
    
    while i < |nums|
    {
        var complement := target - nums[i];
        if complement in hashTable
        {
            return [hashTable[complement], i];
        }
        if nums[i] !in hashTable{
            hashTable := hashTable[nums[i] := i];
        }
        i := i + 1;
    }
    
    return [];
}

method Main()
{
    var result;

    result := twoSum(nums:=[2, 7, 11, 15], target:=9);
    if result != [0, 1]
    {
        print("Test failed: with input (\"nums\":=[2, 7, 11, 15], \"target\":=9) got: ");
        print(result);
        print(" instead of \"[0, 1]\")\n");
    }

    result := twoSum(nums:=[3, 2, 4], target:=6);
    if result != [1, 2]
    {
        print("Test failed: with input (\"nums\":=[3, 2, 4], \"target\":=6) got: ");
        print(result);
        print(" instead of \"[1, 2]\")\n");
    }

    result := twoSum(nums:=[3, 3], target:=6);
    if result != [0, 1]
    {
        print("Test failed: with input (\"nums\":=[3, 3], \"target\":=6) got: ");
        print(result);
        print(" instead of \"[0, 1]\")\n");
    }

    result := twoSum(nums:=[-1, -2, -3, -4, -5], target:=-8);
    if result != [2, 4]
    {
        print("Test failed: with input (\"nums\":=[-1, -2, -3, -4, -5], \"target\":=-8) got: ");
        print(result);
        print(" instead of \"[2, 4]\")\n");
    }

    result := twoSum(nums:=[1000000, -1000000], target:=0);
    if result != [0, 1]
    {
        print("Test failed: with input (\"nums\":=[1000000, -1000000], \"target\":=0) got: ");
        print(result);
        print(" instead of \"[0, 1]\")\n");
    }

    result := twoSum(nums:=[1, 2, 3, 4, 5, 6, 7, 8, 9, 10], target:=19);
    if result != [8, 9]
    {
        print("Test failed: with input (\"nums\":=[1, 2, 3, 4, 5, 6, 7, 8, 9, 10], \"target\":=19) got: ");
        print(result);
        print(" instead of \"[8, 9]\")\n");
    }

}
