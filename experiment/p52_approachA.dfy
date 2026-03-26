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

// Lemma: segmentSum(nums, s, e+1) == segmentSum(nums, s, e) + nums[e]
lemma segmentSumAppend(nums: seq<int>, s: int, e: int)
  requires 0 <= s <= e < |nums|
  ensures segmentSum(nums, s, e + 1) == segmentSum(nums, s, e) + nums[e]
  decreases e - s
{
  if s == e {
  } else {
    segmentSumAppend(nums, s + 1, e);
  }
}

// Lemma: segmentSum of a single element
lemma segmentSumSingle(nums: seq<int>, i: int)
  requires 0 <= i < |nums|
  ensures segmentSum(nums, i, i + 1) == nums[i]
{
}

// Lemma: the Kadane step - extending max subarray ending at i to i+1
// Precondition uses s < i (non-empty subarrays ending at i)
lemma kadaneStep(nums: seq<int>, i: int, currentSum: int, cs: int)
  requires 0 <= i < |nums|
  requires 0 <= cs < i || (cs == 0 && i == 0)
  requires cs <= i
  requires currentSum == segmentSum(nums, cs, i)
  requires forall s :: 0 <= s < i ==> segmentSum(nums, s, i) <= currentSum
  ensures var newSum := if currentSum + nums[i] > nums[i] then currentSum + nums[i] else nums[i];
          var newCs := if currentSum + nums[i] > nums[i] then cs else i;
          newSum == segmentSum(nums, newCs, i + 1) &&
          (forall s {:trigger segmentSum(nums, s, i + 1)} :: 0 <= s < i + 1 ==> segmentSum(nums, s, i + 1) <= newSum)
{
  // First establish the append identity for all relevant starts
  forall s | 0 <= s <= i
    ensures segmentSum(nums, s, i + 1) == segmentSum(nums, s, i) + nums[i]
  {
    segmentSumAppend(nums, s, i);
  }
  segmentSumSingle(nums, i);

  var newSum := if currentSum + nums[i] > nums[i] then currentSum + nums[i] else nums[i];
  var newCs := if currentSum + nums[i] > nums[i] then cs else i;

  // Prove newSum == segmentSum(nums, newCs, i+1)
  if currentSum + nums[i] > nums[i] {
    assert newSum == segmentSum(nums, cs, i) + nums[i];
  } else {
    assert newSum == nums[i];
    assert segmentSum(nums, i, i + 1) == nums[i];
  }

  // Prove all segments ending at i+1 have sum <= newSum
  forall s {:trigger segmentSum(nums, s, i + 1)} | 0 <= s < i + 1
    ensures segmentSum(nums, s, i + 1) <= newSum
  {
    if s < i {
      // segmentSum(nums, s, i+1) = segmentSum(nums, s, i) + nums[i] <= currentSum + nums[i]
      assert segmentSum(nums, s, i) <= currentSum;
      assert segmentSum(nums, s, i + 1) == segmentSum(nums, s, i) + nums[i];
      // currentSum + nums[i] <= newSum (either equal to it, or newSum = nums[i] >= currentSum + nums[i])
    } else {
      // s == i
      assert segmentSum(nums, i, i + 1) == nums[i];
      // newSum >= nums[i] since newSum = max(currentSum + nums[i], nums[i])
    }
  }
}

// Lemma: extending the global max property from i to i+1
// If all segments in [0..i] have sum <= maxSum, and all segments ending at i+1 have sum <= maxSum,
// then all segments in [0..i+1] have sum <= maxSum
lemma extendGlobalMax(nums: seq<int>, i: int, maxSum: int)
  requires 0 <= i < |nums|
  requires forall s: int, e: int :: 0 <= s < e <= i ==> segmentSum(nums, s, e) <= maxSum
  requires forall s {:trigger segmentSum(nums, s, i + 1)} :: 0 <= s < i + 1 ==> segmentSum(nums, s, i + 1) <= maxSum
  ensures forall s: int, e: int :: 0 <= s < e <= i + 1 ==> segmentSum(nums, s, e) <= maxSum
{
  forall s: int, e: int | 0 <= s < e <= i + 1
    ensures segmentSum(nums, s, e) <= maxSum
  {
    if e <= i {
      assert 0 <= s < e <= i;
    } else {
      assert e == i + 1;
      assert 0 <= s < i + 1;
      assert segmentSum(nums, s, i + 1) <= maxSum;
    }
  }
}

// method to be verified
method maxSubArray(nums: seq<int>) returns (maxSum: int)
  requires |nums| >= 1
  ensures  maxSubArrayPost(nums, maxSum)
{
    var currentSum := nums[0];
    maxSum := nums[0];

    // Ghost variables tracking witnesses
    ghost var cs := 0;  // currentSum == segmentSum(nums, cs, i)
    ghost var ms := 0;  // start of maxSum segment
    ghost var me := 1;  // end of maxSum segment

    segmentSumSingle(nums, 0);

    var i := 1;
    while i < |nums|
        invariant 1 <= i <= |nums|
        invariant 0 <= cs < i
        invariant currentSum == segmentSum(nums, cs, i)
        invariant forall s :: 0 <= s < i ==> segmentSum(nums, s, i) <= currentSum
        invariant 0 <= ms < me <= i
        invariant maxSum == segmentSum(nums, ms, me)
        invariant forall s: int, e: int :: 0 <= s < e <= i ==> segmentSum(nums, s, e) <= maxSum
        invariant currentSum <= maxSum
    {
        // Apply the Kadane step lemma
        kadaneStep(nums, i, currentSum, cs);

        ghost var oldMaxSum := maxSum;
        ghost var oldI := i;

        if currentSum + nums[i] > nums[i] {
            currentSum := currentSum + nums[i];
        } else {
            currentSum := nums[i];
            cs := i;
        }

        if currentSum > maxSum {
            maxSum := currentSum;
            ms := cs;
            me := i + 1;
        }

        // At this point:
        // currentSum <= maxSum
        // forall s :: 0 <= s < i+1 ==> segmentSum(nums, s, i+1) <= currentSum <= maxSum (from kadaneStep)
        // But wait, we need currentSum to be the NEW currentSum. Let me think...
        // kadaneStep gives us the newSum property, and we set currentSum = newSum.
        // And currentSum <= maxSum by the if-then-else above.
        // So forall s :: 0 <= s < i+1 ==> segmentSum(nums, s, i+1) <= newSum <= maxSum

        extendGlobalMax(nums, i, maxSum);

        i := i + 1;
    }
}
