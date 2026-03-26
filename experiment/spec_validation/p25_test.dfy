predicate NonDecreasing(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate NoDuplicates(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

function toSet(s: seq<int>): set<int>
{
  set x | x in s
}

predicate IsOrderPreserving(orig: seq<int>, sub: seq<int>)
{
  forall i, j :: 0 <= i < j < |sub| ==>
    exists oi, oj :: 0 <= oi < oj < |orig| &&
      orig[oi] == sub[i] && orig[oj] == sub[j]
}

predicate removeDuplicatesPost(nums: seq<int>, newNums: seq<int>, k: int)
{
  && |newNums| == k
  && k <= |nums|
  && NoDuplicates(newNums)
  && toSet(newNums) == toSet(nums)
  && IsOrderPreserving(nums, newNums)
  && (forall i :: 0 <= i < k ==> exists j :: 0 <= j < |nums| && newNums[i] == nums[j])
}

// method to be verified
method removeDuplicates(nums: seq<int>) returns (newNums: seq<int>, k: int)
  requires |nums| >= 1
  requires NonDecreasing(nums)
  ensures  removeDuplicatesPost(nums, newNums, k)
{
    var result: seq<int> := [];
    result := result + [nums[0]];  // Add first element
    k := 1;
    
    var j := 1;
    while j < |nums|
    {
        if nums[j] != result[k-1]
        {
            result := result + [nums[j]];
            k := k + 1;
        }
        j := j + 1;
    }
    
    newNums := result;
}

method Main()
{
    var result;

    result := removeDuplicates(nums:=[1, 1, 2]);
    if result != 2
    {
        print("Test failed: with input (\"nums\":=[1, 1, 2]) got: ");
        print(result);
        print(" instead of \"2\")\n");
    }

    result := removeDuplicates(nums:=[0, 0, 1, 1, 1, 2, 2, 3, 3, 4]);
    if result != 5
    {
        print("Test failed: with input (\"nums\":=[0, 0, 1, 1, 1, 2, 2, 3, 3, 4]) got: ");
        print(result);
        print(" instead of \"5\")\n");
    }

    result := removeDuplicates(nums:=[1]);
    if result != 1
    {
        print("Test failed: with input (\"nums\":=[1]) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := removeDuplicates(nums:=[1, 1, 1, 1, 1]);
    if result != 1
    {
        print("Test failed: with input (\"nums\":=[1, 1, 1, 1, 1]) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := removeDuplicates(nums:=[-100, -100, -50, 0, 0, 0, 50, 50, 100]);
    if result != 5
    {
        print("Test failed: with input (\"nums\":=[-100, -100, -50, 0, 0, 0, 50, 50, 100]) got: ");
        print(result);
        print(" instead of \"5\")\n");
    }

    result := removeDuplicates(nums:=[-1, 0, 0, 0, 0, 3, 3]);
    if result != 3
    {
        print("Test failed: with input (\"nums\":=[-1, 0, 0, 0, 0, 3, 3]) got: ");
        print(result);
        print(" instead of \"3\")\n");
    }

}
