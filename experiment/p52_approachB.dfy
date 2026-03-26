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
  (exists s:int, e:int ::
      0 <= s < e <= |nums| &&
      segmentSum(nums, s, e) == maxSum) &&
  (forall i:int, j:int ::
      0 <= i < j <= |nums| ==> segmentSum(nums, i, j) <= maxSum)
}

// Lemma: segmentSum(nums, s, e+1) == segmentSum(nums, s, e) + nums[e]
// The recursive definition peels from the front; this lemma lets us extend from the end.
lemma segmentSumExtend(nums: seq<int>, s: int, e: int)
  requires 0 <= s <= e < |nums|
  ensures segmentSum(nums, s, e + 1) == segmentSum(nums, s, e) + nums[e]
  decreases e - s
{
  if s == e {
  } else {
    segmentSumExtend(nums, s + 1, e);
  }
}

method maxSubArray(nums: seq<int>) returns (maxSum: int)
  requires |nums| >= 1
  ensures  maxSubArrayPost(nums, maxSum)
{
    var currentSum := nums[0];
    maxSum := nums[0];

    // Ghost variables to track witnesses
    ghost var cs := 0;    // start index for currentSum's segment
    ghost var ms := 0;    // start index for maxSum's segment
    ghost var me := 1;    // end index for maxSum's segment

    var i := 1;
    while i < |nums|
      invariant 1 <= i <= |nums|
      invariant 0 <= cs < i
      invariant currentSum == segmentSum(nums, cs, i)
      invariant forall s :: 0 <= s < i ==> segmentSum(nums, s, i) <= currentSum
      invariant 0 <= ms < me <= i
      invariant maxSum == segmentSum(nums, ms, me)
      invariant forall s, e :: 0 <= s < e <= i ==> segmentSum(nums, s, e) <= maxSum
      invariant currentSum <= maxSum
    {
        ghost var oldCurrentSum := currentSum;

        if currentSum + nums[i] > nums[i] {
            currentSum := currentSum + nums[i];
            segmentSumExtend(nums, cs, i);
        } else {
            currentSum := nums[i];
            cs := i;
        }

        // Prove: forall s, segmentSum(nums, s, i+1) <= currentSum
        forall s {:trigger segmentSum(nums, s, i + 1)} | 0 <= s < i + 1
          ensures segmentSum(nums, s, i + 1) <= currentSum
        {
          segmentSumExtend(nums, s, i);
          if s < i {
            assert segmentSum(nums, s, i) <= oldCurrentSum;
          }
        }

        if currentSum > maxSum {
            maxSum := currentSum;
            ms := cs;
            me := i + 1;
        }

        // Prove the global upper bound is maintained
        assert forall s, e :: 0 <= s < e <= i + 1 ==> segmentSum(nums, s, e) <= maxSum by {
          forall s, e | 0 <= s < e <= i + 1
            ensures segmentSum(nums, s, e) <= maxSum
          {
            if e == i + 1 {
              assert segmentSum(nums, s, i + 1) <= currentSum;
              assert currentSum <= maxSum;
            }
          }
        }

        i := i + 1;
    }

    assert 0 <= ms < me <= |nums| && segmentSum(nums, ms, me) == maxSum;
    assert forall s, e :: 0 <= s < e <= |nums| ==> segmentSum(nums, s, e) <= maxSum;
}
