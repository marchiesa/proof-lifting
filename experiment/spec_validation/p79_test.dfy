// Auxiliary definitions ---------------------------------------------

function CountOcc(s: seq<int>, v:int): nat
{ 
  |set i | 0 <= i < |s| && s[i] == v| 
}

function Sorted(s: seq<int>): bool
{ 
  forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j] 
}

ghost function IsSubsequence(orig: seq<int>, sub: seq<int>): bool
{
  exists idx: seq<int> ::
       |idx| == |sub| &&
       (forall i :: 0 <= i < |idx| ==> 0 <= idx[i] < |orig|) &&
       (forall i :: 0 <= i < |idx|-1 ==> idx[i] < idx[i+1]) &&
       (forall i :: 0 <= i < |idx| ==> orig[idx[i]] == sub[i])
}

// Post-condition predicate ------------------------------------------

ghost predicate remove_duplicatesPost(nums: array<int>, k:int, oldNums: seq<int>)
  reads nums
{
  0 <= k <= nums.Length &&
  (k <= nums.Length ==>
    var newSeq := nums[..k];
    IsSubsequence(oldNums, newSeq) &&
    Sorted(newSeq) && // still non-decreasing
    (forall v :: v in oldNums ==> CountOcc(newSeq, v) <= 2) && // ≤ 2 copies
    (forall v :: v in oldNums ==> // keep as many as allowed
         CountOcc(newSeq, v) ==
         (if CountOcc(oldNums, v) >= 2 then 2 else CountOcc(oldNums, v)))
  )
}

// method to be verified
method remove_duplicates(nums: array<int>) returns (k:int)
  requires nums.Length >= 1
  requires Sorted(nums[..])      // input is non-decreasing
  ensures remove_duplicatesPost(nums, k, old(nums[..]))
  modifies nums
{
    var i := 0;
    var j := 0;
    while j < nums.Length
    {
        if i < 2 || nums[j] > nums[i-2]
        {
            nums[i] := nums[j];
            i := i + 1;
        }
        j := j + 1;
    }
    return i;
}

method Main()
{
    var result;

    result := remove_duplicates(nums:=[1, 1, 1, 2, 2, 3]);
    if result != 5
    {
        print("Test failed: with input (\"nums\":=[1, 1, 1, 2, 2, 3]) got: ");
        print(result);
        print(" instead of \"5\")\n");
    }

    result := remove_duplicates(nums:=[0, 0, 1, 1, 1, 1, 2, 3, 3]);
    if result != 7
    {
        print("Test failed: with input (\"nums\":=[0, 0, 1, 1, 1, 1, 2, 3, 3]) got: ");
        print(result);
        print(" instead of \"7\")\n");
    }

    result := remove_duplicates(nums:=[1, 1, 1]);
    if result != 2
    {
        print("Test failed: with input (\"nums\":=[1, 1, 1]) got: ");
        print(result);
        print(" instead of \"2\")\n");
    }

    result := remove_duplicates(nums:=[1, 2, 3, 4, 4, 4, 5, 5, 5]);
    if result != 7
    {
        print("Test failed: with input (\"nums\":=[1, 2, 3, 4, 4, 4, 5, 5, 5]) got: ");
        print(result);
        print(" instead of \"7\")\n");
    }

    result := remove_duplicates(nums:=[-1, 0, 0, 0, 0, 3, 3]);
    if result != 5
    {
        print("Test failed: with input (\"nums\":=[-1, 0, 0, 0, 0, 3, 3]) got: ");
        print(result);
        print(" instead of \"5\")\n");
    }

    result := remove_duplicates(nums:=[1]);
    if result != 1
    {
        print("Test failed: with input (\"nums\":=[1]) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := remove_duplicates(nums:=[2, 2, 2, 2, 2]);
    if result != 2
    {
        print("Test failed: with input (\"nums\":=[2, 2, 2, 2, 2]) got: ");
        print(result);
        print(" instead of \"2\")\n");
    }

    result := remove_duplicates(nums:=[-100, -100, -99, -99, -98, 0, 0, 1, 1, 1]);
    if result != 9
    {
        print("Test failed: with input (\"nums\":=[-100, -100, -99, -99, -98, 0, 0, 1, 1, 1]) got: ");
        print(result);
        print(" instead of \"9\")\n");
    }

}
