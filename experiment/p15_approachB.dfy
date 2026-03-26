function AbsoluteDifference(a: int, b: int): int
{
  if a > b then a - b else b - a
}

predicate threeSumClosestPost(nums: seq<int>, target: int, result: int)
{
  |nums| >= 3
  &&
  (exists i,j,k :: 0 <= i < j < k < |nums| &&
                 nums[i] + nums[j] + nums[k] == result)
  &&
  (forall i,j,k :: 0 <= i < j < k < |nums| ==>
       AbsoluteDifference(nums[i] + nums[j] + nums[k], target)
         >= AbsoluteDifference(result, target))
}

// Key lemma: removing an element at index i from a sequence subtracts it from the multiset
lemma RemoveIndexMultiset(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures multiset(s[..i] + s[i+1..]) == multiset(s) - multiset{s[i]}
{
  assert s == s[..i] + [s[i]] + s[i+1..];
  assert multiset(s) == multiset(s[..i]) + multiset{s[i]} + multiset(s[i+1..]);
}

lemma FindInSeq(s: seq<int>, x: int) returns (idx: int)
  requires x in multiset(s)
  ensures 0 <= idx < |s|
  ensures s[idx] == x
{
  // x appears in the multiset, so it must appear somewhere
  idx := 0;
  while idx < |s|
    invariant 0 <= idx <= |s|
    invariant forall p :: 0 <= p < idx ==> s[p] != x
  {
    if s[idx] == x {
      return;
    }
    idx := idx + 1;
  }
  // If we get here, x is not in s, contradiction
  assert x !in multiset(s);
}

// Extract: given multiset{x,y,z} <= multiset(b) and x+y+z == val,
// there exist ordered indices in b summing to val
lemma ExtractTripleIndices(b: seq<int>, x: int, y: int, z: int, val: int)
  requires multiset{x, y, z} <= multiset(b)
  requires x + y + z == val
  ensures exists i,j,k :: 0 <= i < j < k < |b| && b[i] + b[j] + b[k] == val
{
  var i := FindInSeq(b, x);

  var b' := b[..i] + b[i+1..];
  RemoveIndexMultiset(b, i);
  assert multiset(b') == multiset(b) - multiset{x};
  assert multiset{y, z} <= multiset(b');

  var j' := FindInSeq(b', y);

  var b'' := b'[..j'] + b'[j'+1..];
  RemoveIndexMultiset(b', j');
  assert multiset(b'') == multiset(b') - multiset{y};
  assert z in multiset(b'');

  var k' := FindInSeq(b'', z);

  // Map j' back to original index in b
  var j := if j' < i then j' else j' + 1;

  // Verify b[j] == y
  assert b[j] == y by {
    if j' < i {
      assert b'[j'] == b[j'];
    } else {
      assert b'[j'] == b[j' + 1];
    }
  }

  // Map k' to index in b' then to b
  var k_bp := if k' < j' then k' else k' + 1;
  assert b'[k_bp] == z by {
    if k' < j' {
      assert b''[k'] == b'[k'];
    } else {
      assert b''[k'] == b'[k' + 1];
    }
  }
  var k := if k_bp < i then k_bp else k_bp + 1;
  assert b[k] == z by {
    if k_bp < i {
      assert b'[k_bp] == b[k_bp];
    } else {
      assert b'[k_bp] == b[k_bp + 1];
    }
  }

  assert i != j;
  assert i != k;
  assert j != k;
  assert b[i] + b[j] + b[k] == val;

  // Sort the three distinct indices
  var lo, mid, hi: int;
  if i < j {
    if j < k { lo := i; mid := j; hi := k; }
    else if i < k { lo := i; mid := k; hi := j; }
    else { lo := k; mid := i; hi := j; }
  } else {
    if i < k { lo := j; mid := i; hi := k; }
    else if j < k { lo := j; mid := k; hi := i; }
    else { lo := k; mid := j; hi := i; }
  }
  assert 0 <= lo < mid < hi < |b|;
  assert b[lo] + b[mid] + b[hi] == val;
}

lemma MultisetSubmultisetFromDistinctIndices(s: seq<int>, i: int, j: int, k: int)
  requires 0 <= i < j < k < |s|
  ensures multiset{s[i], s[j], s[k]} <= multiset(s)
{
  assert s == s[..i] + [s[i]] + s[i+1..j] + [s[j]] + s[j+1..k] + [s[k]] + s[k+1..];
}

// If two sequences have the same multiset, any triple sum achievable in one
// is achievable in the other.
lemma MultisetTripleSumEquiv(a: seq<int>, b: seq<int>, val: int)
  requires multiset(a) == multiset(b)
  requires exists i,j,k :: 0 <= i < j < k < |a| && a[i] + a[j] + a[k] == val
  ensures  exists i,j,k :: 0 <= i < j < k < |b| && b[i] + b[j] + b[k] == val
{
  var i, j, k :| 0 <= i < j < k < |a| && a[i] + a[j] + a[k] == val;
  var x, y, z := a[i], a[j], a[k];
  MultisetSubmultisetFromDistinctIndices(a, i, j, k);
  assert multiset{x, y, z} <= multiset(a);
  assert multiset{x, y, z} <= multiset(b);
  ExtractTripleIndices(b, x, y, z, val);
}

// Reverse direction: for a specific triple in b, the same sum is achievable in a
lemma MultisetTripleSumEquivReverse(a: seq<int>, b: seq<int>, i: int, j: int, k: int)
  requires multiset(a) == multiset(b)
  requires 0 <= i < j < k < |b|
  ensures exists i',j',k' :: 0 <= i' < j' < k' < |a| && a[i'] + a[j'] + a[k'] == b[i] + b[j] + b[k]
{
  var val := b[i] + b[j] + b[k];
  MultisetTripleSumEquiv(b, a, val);
}

predicate Sorted(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  forall p, q :: lo <= p < q < hi ==> a[p] <= a[q]
}

predicate SeqSorted(s: seq<int>)
{
  forall p, q :: 0 <= p < q < |s| ==> s[p] <= s[q]
}

predicate IsTripleSumOf(v: int, s: seq<int>)
{
  exists i, j, k :: 0 <= i < j < k < |s| && s[i] + s[j] + s[k] == v
}

predicate IsClosestUpTo(closest: int, arr: seq<int>, target: int, bound: int)
  requires 0 <= bound <= |arr|
{
  forall a, b, c :: 0 <= a < bound && a < b < c < |arr| ==>
    AbsoluteDifference(arr[a] + arr[b] + arr[c], target) >= AbsoluteDifference(closest, target)
}

method threeSumClosest(nums: seq<int>, target: int) returns (result: int)
  requires |nums| >= 3
  ensures  threeSumClosestPost(nums, target, result)
{
    var n := |nums|;
    if n < 3 { return 0; }

    var arr := new int[n];
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant forall p :: 0 <= p < i ==> arr[p] == nums[p]
    {
        arr[i] := nums[i];
        i := i + 1;
    }

    assert arr[..] == nums;

    // Selection sort
    i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant arr.Length == n
      invariant multiset(arr[..]) == multiset(nums)
      invariant Sorted(arr, 0, i)
      invariant forall p, q :: 0 <= p < i <= q < n ==> arr[p] <= arr[q]
    {
        var j := i + 1;
        while j < n
          invariant i + 1 <= j <= n
          invariant arr.Length == n
          invariant multiset(arr[..]) == multiset(nums)
          invariant Sorted(arr, 0, i)
          invariant forall p, q :: 0 <= p < i <= q < n ==> arr[p] <= arr[q]
          invariant forall q :: i < q < j ==> arr[i] <= arr[q]
        {
            if arr[j] < arr[i] {
                var temp := arr[i];
                arr[i] := arr[j];
                arr[j] := temp;
            }
            j := j + 1;
        }
        i := i + 1;
    }

    assert Sorted(arr, 0, n);
    assert multiset(arr[..]) == multiset(nums);

    ghost var sortedSeq := arr[..];
    assert SeqSorted(sortedSeq);

    var closest := arr[0] + arr[1] + arr[2];

    assert IsTripleSumOf(closest, sortedSeq) by {
      assert sortedSeq[0] + sortedSeq[1] + sortedSeq[2] == closest;
    }

    closest := OuterLoop(arr, n, target, closest, sortedSeq, nums);

    result := closest;
}

// Factor out the main search into a separate method to help verification
method OuterLoop(arr: array<int>, n: int, target: int, initClosest: int,
                 ghost sortedSeq: seq<int>, ghost nums: seq<int>)
  returns (closest: int)
  requires arr.Length == n
  requires n >= 3
  requires arr[..] == sortedSeq
  requires SeqSorted(sortedSeq)
  requires multiset(sortedSeq) == multiset(nums)
  requires |nums| == n
  requires IsTripleSumOf(initClosest, sortedSeq)
  ensures IsTripleSumOf(closest, sortedSeq)
  ensures forall a, b, c :: 0 <= a < b < c < n ==>
    AbsoluteDifference(sortedSeq[a] + sortedSeq[b] + sortedSeq[c], target) >= AbsoluteDifference(closest, target)
  ensures threeSumClosestPost(nums, target, closest)
{
    closest := initClosest;
    var i := 0;

    while i < n - 2
      invariant 0 <= i <= n - 2
      invariant arr.Length == n
      invariant arr[..] == sortedSeq
      invariant IsTripleSumOf(closest, sortedSeq)
      invariant forall a, b, c :: 0 <= a < i && a < b < c < n ==>
        AbsoluteDifference(sortedSeq[a] + sortedSeq[b] + sortedSeq[c], target) >= AbsoluteDifference(closest, target)
    {
        closest := InnerTwoPointer(arr, n, target, closest, i, sortedSeq);
        i := i + 1;
    }

    // Transfer to nums
    TransferToNums(sortedSeq, nums, closest, target, n);
}

// Helper lemma for the left-move case in two-pointer
lemma LeftMoveLemma(sortedSeq: seq<int>, outerI: int, left: int, right: int, n: int,
                    curSum: int, target: int, closest: int)
  requires |sortedSeq| == n
  requires SeqSorted(sortedSeq)
  requires 0 <= outerI < left < right < n
  requires curSum == sortedSeq[outerI] + sortedSeq[left] + sortedSeq[right]
  requires curSum < target
  requires AbsoluteDifference(closest, target) <= AbsoluteDifference(curSum, target)
  ensures forall c :: left < c <= right ==>
    AbsoluteDifference(sortedSeq[outerI] + sortedSeq[left] + sortedSeq[c], target) >= AbsoluteDifference(closest, target)
{
  forall c | left < c <= right
    ensures AbsoluteDifference(sortedSeq[outerI] + sortedSeq[left] + sortedSeq[c], target) >= AbsoluteDifference(closest, target)
  {
    assert sortedSeq[c] <= sortedSeq[right];
    var s := sortedSeq[outerI] + sortedSeq[left] + sortedSeq[c];
    assert s <= curSum;
    assert s <= curSum < target;
    assert AbsoluteDifference(s, target) == target - s;
    assert AbsoluteDifference(curSum, target) == target - curSum;
    assert target - s >= target - curSum;
  }
}

// Helper lemma for the right-move case in two-pointer
lemma RightMoveLemma(sortedSeq: seq<int>, outerI: int, left: int, right: int, n: int,
                     curSum: int, target: int, closest: int)
  requires |sortedSeq| == n
  requires SeqSorted(sortedSeq)
  requires 0 <= outerI < left < right < n
  requires curSum == sortedSeq[outerI] + sortedSeq[left] + sortedSeq[right]
  requires curSum > target
  requires AbsoluteDifference(closest, target) <= AbsoluteDifference(curSum, target)
  ensures forall b :: left <= b < right ==>
    AbsoluteDifference(sortedSeq[outerI] + sortedSeq[b] + sortedSeq[right], target) >= AbsoluteDifference(closest, target)
{
  forall b | left <= b < right
    ensures AbsoluteDifference(sortedSeq[outerI] + sortedSeq[b] + sortedSeq[right], target) >= AbsoluteDifference(closest, target)
  {
    assert sortedSeq[b] >= sortedSeq[left];
    var s := sortedSeq[outerI] + sortedSeq[b] + sortedSeq[right];
    assert s >= curSum;
    assert s >= curSum > target;
    assert AbsoluteDifference(s, target) == s - target;
    assert AbsoluteDifference(curSum, target) == curSum - target;
    assert s - target >= curSum - target;
  }
}

method InnerTwoPointer(arr: array<int>, n: int, target: int, initClosest: int,
                       outerI: int, ghost sortedSeq: seq<int>)
  returns (closest: int)
  requires arr.Length == n
  requires n >= 3
  requires 0 <= outerI < n - 2
  requires arr[..] == sortedSeq
  requires SeqSorted(sortedSeq)
  requires IsTripleSumOf(initClosest, sortedSeq)
  requires forall a, b, c :: 0 <= a < outerI && a < b < c < n ==>
    AbsoluteDifference(sortedSeq[a] + sortedSeq[b] + sortedSeq[c], target) >= AbsoluteDifference(initClosest, target)
  ensures arr[..] == sortedSeq
  ensures IsTripleSumOf(closest, sortedSeq)
  ensures forall a, b, c :: 0 <= a <= outerI && a < b < c < n ==>
    AbsoluteDifference(sortedSeq[a] + sortedSeq[b] + sortedSeq[c], target) >= AbsoluteDifference(closest, target)
{
    closest := initClosest;
    var left := outerI + 1;
    var right := n - 1;

    while left < right
      invariant outerI + 1 <= left
      invariant right < n
      invariant left <= right + 1
      invariant arr.Length == n
      invariant arr[..] == sortedSeq
      invariant IsTripleSumOf(closest, sortedSeq)
      invariant forall a, b, c :: 0 <= a < outerI && a < b < c < n ==>
        AbsoluteDifference(sortedSeq[a] + sortedSeq[b] + sortedSeq[c], target) >= AbsoluteDifference(closest, target)
      invariant forall b, c :: outerI < b < c < n && (b < left || c > right) ==>
        AbsoluteDifference(sortedSeq[outerI] + sortedSeq[b] + sortedSeq[c], target) >= AbsoluteDifference(closest, target)
    {
        var curSum := arr[outerI] + arr[left] + arr[right];
        assert curSum == sortedSeq[outerI] + sortedSeq[left] + sortedSeq[right];

        if curSum == target {
            closest := curSum;
            assert IsTripleSumOf(closest, sortedSeq);
            assert AbsoluteDifference(closest, target) == 0;
            return;
        }

        ghost var oldClosest := closest;
        var diffCur := AbsoluteDifference(curSum, target);
        var diffClosest := AbsoluteDifference(closest, target);

        if diffCur < diffClosest {
            closest := curSum;
            assert IsTripleSumOf(closest, sortedSeq);
        }

        // After potential update, closest is at least as good as curSum
        assert AbsoluteDifference(closest, target) <= AbsoluteDifference(curSum, target);

        if curSum < target {
            LeftMoveLemma(sortedSeq, outerI, left, right, n, curSum, target, closest);
            left := left + 1;
        } else {
            assert curSum > target;
            RightMoveLemma(sortedSeq, outerI, left, right, n, curSum, target, closest);
            right := right - 1;
        }
    }
}

lemma TransferToNums(sortedSeq: seq<int>, nums: seq<int>, closest: int, target: int, n: int)
  requires |sortedSeq| == n
  requires |nums| == n
  requires n >= 3
  requires multiset(sortedSeq) == multiset(nums)
  requires IsTripleSumOf(closest, sortedSeq)
  requires forall a, b, c :: 0 <= a < b < c < n ==>
    AbsoluteDifference(sortedSeq[a] + sortedSeq[b] + sortedSeq[c], target) >= AbsoluteDifference(closest, target)
  ensures threeSumClosestPost(nums, target, closest)
{
  // closest is a triple sum of sortedSeq, transfer to nums
  MultisetTripleSumEquiv(sortedSeq, nums, closest);

  // Optimality: for any triple in nums, there's one in sortedSeq with same sum
  forall ii, jj, kk | 0 <= ii < jj < kk < |nums|
    ensures AbsoluteDifference(nums[ii] + nums[jj] + nums[kk], target) >= AbsoluteDifference(closest, target)
  {
    MultisetTripleSumEquivReverse(sortedSeq, nums, ii, jj, kk);
    var a, b, c :| 0 <= a < b < c < |sortedSeq| && sortedSeq[a] + sortedSeq[b] + sortedSeq[c] == nums[ii] + nums[jj] + nums[kk];
  }
}
