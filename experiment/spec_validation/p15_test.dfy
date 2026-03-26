function AbsoluteDifference(a: int, b: int): int
{
  if a > b then a - b else b - a
}

predicate threeSumClosestPost(nums: seq<int>, target: int, result: int)
{
  |nums| >= 3
  &&
  // There is at least one triple whose sum equals the reported result
  (exists i,j,k :: 0 <= i < j < k < |nums| &&
                 nums[i] + nums[j] + nums[k] == result)
  &&
  // The reported result is not farther from the target than any other triple sum
  (forall i,j,k :: 0 <= i < j < k < |nums| ==>
       AbsoluteDifference(nums[i] + nums[j] + nums[k], target) 
         >= AbsoluteDifference(result, target))
}

// method to be verified
method threeSumClosest(nums: seq<int>, target: int) returns (result: int)
  requires |nums| >= 3
  ensures  threeSumClosestPost(nums, target, result)
{
    var n := |nums|;
    if n < 3 { return 0; }  // handle invalid input

    // Convert sequence to array for sorting
    var arr := new int[n];
    var i := 0;
    while i < n {
        arr[i] := nums[i];
        i := i + 1;
    }

    // Sort array
    i := 0;
    while i < n {
        var j := i + 1;
        while j < n {
            if arr[j] < arr[i] {
                var temp := arr[i];
                arr[i] := arr[j];
                arr[j] := temp;
            }
            j := j + 1;
        }
        i := i + 1;
    }

    // Initialize closest with sum of first three elements
    var closest := arr[0] + arr[1] + arr[2];

    i := 0;
    while i < n - 2 {
        var left := i + 1;
        var right := n - 1;

        while left < right {
            var curSum := arr[i] + arr[left] + arr[right];
            
            if curSum == target {
                return curSum;
            }

            // Calculate absolute differences
            var diffCur := if target > curSum then target - curSum else curSum - target;
            var diffClosest := if target > closest then target - closest else closest - target;

            if diffCur < diffClosest {
                closest := curSum;
            }

            if curSum < target {
                left := left + 1;
            } else {
                right := right - 1;
            }
        }
        i := i + 1;
    }

    return closest;
}

method Main()
{
    var result;

    result := threeSumClosest(nums:=[-4, -1, 1, 2], target:=1);
    if result != 2
    {
        print("Test failed: with input (\"nums\":=[-4, -1, 1, 2], \"target\":=1) got: ");
        print(result);
        print(" instead of \"2\")\n");
    }

    result := threeSumClosest(nums:=[0, 0, 0], target:=1);
    if result != 0
    {
        print("Test failed: with input (\"nums\":=[0, 0, 0], \"target\":=1) got: ");
        print(result);
        print(" instead of \"0\")\n");
    }

    result := threeSumClosest(nums:=[-1000, -999, -998, 1000], target:=0);
    if result != -997
    {
        print("Test failed: with input (\"nums\":=[-1000, -999, -998, 1000], \"target\":=0) got: ");
        print(result);
        print(" instead of \"-997\")\n");
    }

    result := threeSumClosest(nums:=[0, 1, 1, 1], target:=100);
    if result != 3
    {
        print("Test failed: with input (\"nums\":=[0, 1, 1, 1], \"target\":=100) got: ");
        print(result);
        print(" instead of \"3\")\n");
    }

    result := threeSumClosest(nums:=[-100, -50, 0, 50, 100], target:=-30);
    if result != -50
    {
        print("Test failed: with input (\"nums\":=[-100, -50, 0, 50, 100], \"target\":=-30) got: ");
        print(result);
        print(" instead of \"-50\")\n");
    }

    result := threeSumClosest(nums:=[-5, -5, -4, 0, 0, 3, 3, 4, 5], target:=-2);
    if result != -2
    {
        print("Test failed: with input (\"nums\":=[-5, -5, -4, 0, 0, 3, 3, 4, 5], \"target\":=-2) got: ");
        print(result);
        print(" instead of \"-2\")\n");
    }

}
