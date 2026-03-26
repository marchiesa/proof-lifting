predicate Sorted(s: seq<int>)
{
  forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate SeqPermutation(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}

ghost predicate findMedianSortedArraysPost(nums1: seq<int>, nums2: seq<int>, result: real)
{
  |nums1| + |nums2| >= 1 &&
  exists merged: seq<int> ::
       |merged| == |nums1| + |nums2| &&
       SeqPermutation(merged, nums1 + nums2) &&
       Sorted(merged) &&
       (if |merged| % 2 == 1
        then result == merged[|merged|/2] as real
        else result == (merged[|merged|/2 - 1] as real + merged[|merged|/2] as real) / 2.0)
}

// method to be verified
method findMedianSortedArrays(nums1: seq<int>, nums2: seq<int>) returns (result: real)
  requires Sorted(nums1) && Sorted(nums2)
  requires |nums1| + |nums2| >= 1
  requires |nums1| <= 1000 && |nums2| <= 1000
  ensures findMedianSortedArraysPost(nums1, nums2, result)
{
    if |nums1| > |nums2| {
        result := findMedianSortedArrays(nums2, nums1);
        return;
    }

    var x, y := |nums1|, |nums2|;
    var low, high := 0, x;

    while low <= high
    {
        var partition_x := (low + high) / 2;
        var partition_y := (x + y + 1) / 2 - partition_x;

        var max_left_x: real;
        var min_right_x: real;
        var max_left_y: real;
        var min_right_y: real;

        if partition_x == 0 { max_left_x := -1000000.0; }
        else { max_left_x := nums1[partition_x - 1] as real; }

        if partition_x == x { min_right_x := 1000000.0; }
        else { min_right_x := nums1[partition_x] as real; }

        if partition_y == 0 { max_left_y := -1000000.0; }
        else { max_left_y := nums2[partition_y - 1] as real; }

        if partition_y == y { min_right_y := 1000000.0; }
        else { min_right_y := nums2[partition_y] as real; }

        if max_left_x <= min_right_y && max_left_y <= min_right_x {
            if (x + y) % 2 == 0 {
                result := (if max_left_x > max_left_y then max_left_x else max_left_y) + 
                         (if min_right_x < min_right_y then min_right_x else min_right_y);
                result := result / 2.0;
                return;
            } else {
                result := if max_left_x > max_left_y then max_left_x else max_left_y;
                return;
            }
        } else if max_left_x > min_right_y {
            high := partition_x - 1;
        } else {
            low := partition_x + 1;
        }
    }

    result := 0.0;
}

method Main()
{
    var result;

    result := findMedianSortedArrays(nums1:=[1, 3], nums2:=[2]);
    if result != 2
    {
        print("Test failed: with input (\"nums1\":=[1, 3], \"nums2\":=[2]) got: ");
        print(result);
        print(" instead of \"2\")\n");
    }

    result := findMedianSortedArrays(nums1:=[1, 2], nums2:=[3, 4]);
    if result != 2.5
    {
        print("Test failed: with input (\"nums1\":=[1, 2], \"nums2\":=[3, 4]) got: ");
        print(result);
        print(" instead of \"2.5\")\n");
    }

    result := findMedianSortedArrays(nums1:=[], nums2:=[1]);
    if result != 1
    {
        print("Test failed: with input (\"nums1\":=[], \"nums2\":=[1]) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := findMedianSortedArrays(nums1:=[1], nums2:=[]);
    if result != 1
    {
        print("Test failed: with input (\"nums1\":=[1], \"nums2\":=[]) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := findMedianSortedArrays(nums1:=[1, 3, 5], nums2:=[2, 4, 6]);
    if result != 3.5
    {
        print("Test failed: with input (\"nums1\":=[1, 3, 5], \"nums2\":=[2, 4, 6]) got: ");
        print(result);
        print(" instead of \"3.5\")\n");
    }

    result := findMedianSortedArrays(nums1:=[-106], nums2:=[106]);
    if result != 0.0
    {
        print("Test failed: with input (\"nums1\":=[-106], \"nums2\":=[106]) got: ");
        print(result);
        print(" instead of \"0.0\")\n");
    }

    result := findMedianSortedArrays(nums1:=[0, 0], nums2:=[0, 0]);
    if result != 0.0
    {
        print("Test failed: with input (\"nums1\":=[0, 0], \"nums2\":=[0, 0]) got: ");
        print(result);
        print(" instead of \"0.0\")\n");
    }

    result := findMedianSortedArrays(nums1:=[-1, 3, 5, 7, 9], nums2:=[2, 4, 6, 8, 10]);
    if result != 5.5
    {
        print("Test failed: with input (\"nums1\":=[-1, 3, 5, 7, 9], \"nums2\":=[2, 4, 6, 8, 10]) got: ");
        print(result);
        print(" instead of \"5.5\")\n");
    }

}
