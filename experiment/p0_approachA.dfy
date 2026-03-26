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
        invariant 0 <= i <= |nums|
        invariant forall v :: v in hashTable ==> 0 <= hashTable[v] < i && hashTable[v] < |nums| && nums[hashTable[v]] == v
        invariant forall k :: 0 <= k < i ==> nums[k] in hashTable
        invariant forall j, k :: 0 <= j < i && 0 <= k < i && j != k ==> nums[j] + nums[k] != target
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

    // The loop completed: i == |nums|, so all pairs (j,k) with j,k < |nums| have nums[j]+nums[k] != target
    // This contradicts the precondition
    assert forall j, k :: 0 <= j < |nums| && 0 <= k < |nums| && j != k ==> nums[j] + nums[k] != target;
    assert false;
    return [];
}

