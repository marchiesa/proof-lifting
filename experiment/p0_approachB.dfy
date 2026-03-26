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
        invariant forall v :: v in hashTable ==> 0 <= hashTable[v] < i
        invariant forall v :: v in hashTable ==> hashTable[v] < |nums|
        invariant forall v :: v in hashTable ==> nums[hashTable[v]] == v
        invariant forall j :: 0 <= j < i ==> nums[j] in hashTable
        invariant forall a, b :: 0 <= a < i && 0 <= b < i && a != b && nums[a] + nums[b] == target ==> false
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

