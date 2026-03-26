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

ghost predicate tripleAchievableOrdered(s: seq<int>, v: int)
{
  exists i, j, k :: 0 <= i < j < k < |s| && s[i] + s[j] + s[k] == v
}

lemma swapPreservesMultiset(s: seq<int>, i: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
}

lemma removeIndexMultiset(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures multiset(s[..i] + s[i+1..]) == multiset(s) - multiset{s[i]}
{
  assert s == s[..i] + [s[i]] + s[i+1..];
}

lemma removeIndexMapping(s: seq<int>, i: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s| - 1
  ensures var s' := s[..i] + s[i+1..];
          var j' := if j < i then j else j + 1;
          0 <= j' < |s| && j' != i && s'[j] == s[j']
{
}

lemma multisetTripleTransfer(a: seq<int>, b: seq<int>, v: int)
  requires multiset(a) == multiset(b)
  requires tripleAchievableOrdered(a, v)
  ensures tripleAchievableOrdered(b, v)
{
  var i, j, k :| 0 <= i < j < k < |a| && a[i] + a[j] + a[k] == v;
  assert |a| == |b|;
  var vi, vj, vk := a[i], a[j], a[k];
  ghost var msA := multiset(a);
  ghost var msB := multiset(b);

  assert vi in multiset(b);
  var i' :| 0 <= i' < |b| && b[i'] == vi;

  ghost var b1 := b[..i'] + b[i'+1..];
  removeIndexMultiset(b, i');

  if vi == vj {
    indexCountHelper(a, vi, i, j);
  }
  assert vj in msA - multiset{vi};
  assert vj in multiset(b1);
  var j1 :| 0 <= j1 < |b1| && b1[j1] == vj;
  removeIndexMapping(b, i', j1);
  var j' := if j1 < i' then j1 else j1 + 1;

  ghost var b2 := b1[..j1] + b1[j1+1..];
  removeIndexMultiset(b1, j1);
  indexCountLemma3(a, i, j, k);
  assert vk in msA - multiset{vi} - multiset{vj};
  assert vk in multiset(b2);
  var k1 :| 0 <= k1 < |b2| && b2[k1] == vk;
  removeIndexMapping(b1, j1, k1);
  var kInB1 := if k1 < j1 then k1 else k1 + 1;
  removeIndexMapping(b, i', kInB1);
  var k' := if kInB1 < i' then kInB1 else kInB1 + 1;

  if k' == j' {
    if j1 < i' && kInB1 < i' {
    } else if j1 >= i' && kInB1 >= i' {
    } else if j1 < i' && kInB1 >= i' {
      assert j1 < i' <= kInB1;
      assert false;
    } else {
      assert kInB1 < i' <= j1;
      assert false;
    }
    assert false;
  }

  assert b[i'] + b[j'] + b[k'] == v;
  if i' < j' {
    if j' < k' {
    } else if i' < k' {
    } else {
    }
  } else {
    if i' < k' {
    } else if j' < k' {
    } else {
    }
  }
}

lemma indexCountHelper(s: seq<int>, v: int, i: int, j: int)
  requires 0 <= i < j < |s|
  requires s[i] == v && s[j] == v
  ensures multiset(s)[v] >= 2
{
  assert s == s[..i] + [s[i]] + s[i+1..j] + [s[j]] + s[j+1..];
}

lemma indexCountHelper3(s: seq<int>, v: int, i: int, j: int, k: int)
  requires 0 <= i < j < k < |s|
  requires s[i] == v && s[j] == v && s[k] == v
  ensures multiset(s)[v] >= 3
{
  assert s == s[..i] + [s[i]] + s[i+1..j] + [s[j]] + s[j+1..k] + [s[k]] + s[k+1..];
}

lemma indexCountLemma3(s: seq<int>, i: int, j: int, k: int)
  requires 0 <= i < j < k < |s|
  ensures s[k] in multiset(s) - multiset{s[i]} - multiset{s[j]}
{
  var v := s[k];
  var ms := multiset(s);
  if s[i] == v && s[j] == v {
    indexCountHelper3(s, v, i, j, k);
  } else if s[i] == v {
    indexCountHelper(s, v, i, k);
  } else if s[j] == v {
    indexCountHelper(s, v, j, k);
  }
}

// Selection sort extracted
method selectionSort(arr: array<int>, ghost nums: seq<int>)
  requires arr.Length == |nums|
  requires multiset(arr[..]) == multiset(nums)
  modifies arr
  ensures multiset(arr[..]) == multiset(nums)
  ensures forall a, b :: 0 <= a < b < arr.Length ==> arr[a] <= arr[b]
{
  var n := arr.Length;
  var i := 0;
  while i < n
      invariant 0 <= i <= n
      invariant multiset(arr[..]) == multiset(nums)
      invariant forall a, b :: 0 <= a < i && i <= b < n ==> arr[a] <= arr[b]
      invariant forall a, b :: 0 <= a < b < i ==> arr[a] <= arr[b]
  {
      var j := i + 1;
      while j < n
          invariant i + 1 <= j <= n
          invariant multiset(arr[..]) == multiset(nums)
          invariant forall a, b :: 0 <= a < i && i <= b < n ==> arr[a] <= arr[b]
          invariant forall a, b :: 0 <= a < b < i ==> arr[a] <= arr[b]
          invariant forall b :: i + 1 <= b < j ==> arr[i] <= arr[b]
      {
          if arr[j] < arr[i] {
              ghost var oldArr := arr[..];
              var temp := arr[i];
              arr[i] := arr[j];
              arr[j] := temp;
              assert arr[..] == oldArr[i := oldArr[j]][j := oldArr[i]];
              swapPreservesMultiset(oldArr, i, j);
          }
          j := j + 1;
      }
      i := i + 1;
  }
}

// Helper for the optimality transfer: if optimal over arr, then optimal over nums
lemma optimalityTransfer(arr: seq<int>, nums: seq<int>, closest: int, target: int)
  requires multiset(arr) == multiset(nums)
  requires |arr| == |nums|
  requires forall a, b, c :: 0 <= a < b < c < |arr| ==>
      AbsoluteDifference(arr[a] + arr[b] + arr[c], target) >= AbsoluteDifference(closest, target)
  ensures forall a, b, c :: 0 <= a < b < c < |nums| ==>
      AbsoluteDifference(nums[a] + nums[b] + nums[c], target) >= AbsoluteDifference(closest, target)
{
  forall a, b, c | 0 <= a < b < c < |nums|
    ensures AbsoluteDifference(nums[a] + nums[b] + nums[c], target) >= AbsoluteDifference(closest, target)
  {
    var v := nums[a] + nums[b] + nums[c];
    assert tripleAchievableOrdered(nums, v);
    multisetTripleTransfer(nums, arr, v);
    var a', b', c' :| 0 <= a' < b' < c' < |arr| && arr[a'] + arr[b'] + arr[c'] == v;
  }
}

// Two-pointer step lemmas
lemma twoPointerLeftStep(arr: seq<int>, i: int, left: int, right: int, closest: int, target: int)
  requires 0 <= i < left < right < |arr|
  requires forall a, b :: 0 <= a < b < |arr| ==> arr[a] <= arr[b]
  requires arr[i] + arr[left] + arr[right] < target
  requires AbsoluteDifference(arr[i] + arr[left] + arr[right], target) >= AbsoluteDifference(closest, target)
  ensures forall c :: left < c <= right ==>
    AbsoluteDifference(arr[i] + arr[left] + arr[c], target) >= AbsoluteDifference(closest, target)
{
  forall c | left < c <= right
    ensures AbsoluteDifference(arr[i] + arr[left] + arr[c], target) >= AbsoluteDifference(closest, target)
  {
    assert arr[c] <= arr[right];
    var sum_c := arr[i] + arr[left] + arr[c];
    assert sum_c <= arr[i] + arr[left] + arr[right];
    assert sum_c < target;
  }
}

lemma twoPointerRightStep(arr: seq<int>, i: int, left: int, right: int, closest: int, target: int)
  requires 0 <= i < left < right < |arr|
  requires forall a, b :: 0 <= a < b < |arr| ==> arr[a] <= arr[b]
  requires arr[i] + arr[left] + arr[right] > target
  requires AbsoluteDifference(arr[i] + arr[left] + arr[right], target) >= AbsoluteDifference(closest, target)
  ensures forall b :: left <= b < right ==>
    AbsoluteDifference(arr[i] + arr[b] + arr[right], target) >= AbsoluteDifference(closest, target)
{
  forall b | left <= b < right
    ensures AbsoluteDifference(arr[i] + arr[b] + arr[right], target) >= AbsoluteDifference(closest, target)
  {
    assert arr[b] >= arr[left];
    var sum_b := arr[i] + arr[b] + arr[right];
    assert sum_b >= arr[i] + arr[left] + arr[right];
    assert sum_b > target;
  }
}

// Inner two-pointer loop as a separate method
method twoPointerSearch(arr: array<int>, i: int, target: int,
                        closestIn: int, ghost ciIn: int, ghost cjIn: int, ghost ckIn: int)
    returns (closestOut: int, ghost ciOut: int, ghost cjOut: int, ghost ckOut: int)
  requires arr.Length >= 3
  requires 0 <= i < arr.Length - 2
  requires forall a, b :: 0 <= a < b < arr.Length ==> arr[a] <= arr[b]
  requires 0 <= ciIn < cjIn < ckIn < arr.Length
  requires closestIn == arr[ciIn] + arr[cjIn] + arr[ckIn]
  ensures 0 <= ciOut < cjOut < ckOut < arr.Length
  ensures closestOut == arr[ciOut] + arr[cjOut] + arr[ckOut]
  ensures AbsoluteDifference(closestOut, target) <= AbsoluteDifference(closestIn, target)
  ensures forall b, c :: i < b < c < arr.Length ==>
      AbsoluteDifference(arr[i] + arr[b] + arr[c], target) >= AbsoluteDifference(closestOut, target)
{
  var n := arr.Length;
  closestOut := closestIn;
  ciOut := ciIn;
  cjOut := cjIn;
  ckOut := ckIn;
  var left := i + 1;
  var right := n - 1;

  while left < right
      invariant i + 1 <= left
      invariant left - 1 <= right <= n - 1
      invariant 0 <= ciOut < cjOut < ckOut < n
      invariant closestOut == arr[ciOut] + arr[cjOut] + arr[ckOut]
      invariant AbsoluteDifference(closestOut, target) <= AbsoluteDifference(closestIn, target)
      invariant forall b, c :: i < b < c < n && (b < left || c > right) ==>
          AbsoluteDifference(arr[i] + arr[b] + arr[c], target) >= AbsoluteDifference(closestOut, target)
  {
    var curSum := arr[i] + arr[left] + arr[right];

    if curSum == target {
      closestOut := curSum;
      ciOut := i;
      cjOut := left;
      ckOut := right;
      assert AbsoluteDifference(closestOut, target) == 0;
      return;
    }

    ghost var prevClosest := closestOut;
    ghost var prevCi, prevCj, prevCk := ciOut, cjOut, ckOut;

    var diffCur := AbsoluteDifference(curSum, target);
    var diffClosest := AbsoluteDifference(closestOut, target);

    if diffCur < diffClosest {
      closestOut := curSum;
      ciOut := i;
      cjOut := left;
      ckOut := right;
    }

    if curSum < target {
      twoPointerLeftStep(arr[..], i, left, right, closestOut, target);

      // We need to maintain: for b < left+1 || c > right, the triple is dominated
      // Old invariant: b < left || c > right ==> dominated by prevClosest
      // New triples to cover: b == left && c <= right (except b==left, c==right which is curSum)
      // From twoPointerLeftStep: for c in (left, right], arr[i]+arr[left]+arr[c] >= closestOut
      // And the case c == left+1..right, b == left is covered
      // What about b == left, c == right? That's curSum, and diffCur >= diffClosest >= closestOut diff

      left := left + 1;
    } else {
      twoPointerRightStep(arr[..], i, left, right, closestOut, target);

      right := right - 1;
    }
  }

  // When left >= right, for any b, c with i < b < c < n:
  // either b < left (covered) or c > right (covered)
  // because if b >= left and c <= right, then b >= left > right >= c, contradicting b < c
  forall b, c | i < b < c < n
    ensures AbsoluteDifference(arr[i] + arr[b] + arr[c], target) >= AbsoluteDifference(closestOut, target)
  {
    if b < left {
    } else {
      // b >= left >= right + 1 > right, so c > b > right, meaning c > right
      assert c > right;
    }
  }
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
        invariant arr.Length == n
        invariant forall idx :: 0 <= idx < i ==> arr[idx] == nums[idx]
    {
        arr[i] := nums[i];
        i := i + 1;
    }
    assert arr[..] == nums;

    selectionSort(arr, nums);

    var closest := arr[0] + arr[1] + arr[2];
    ghost var ci, cj, ck := 0, 1, 2;

    i := 0;
    while i < n - 2
        invariant 0 <= i <= n - 2
        invariant arr.Length == n
        invariant multiset(arr[..]) == multiset(nums)
        invariant forall a, b :: 0 <= a < b < n ==> arr[a] <= arr[b]
        invariant 0 <= ci < cj < ck < n
        invariant closest == arr[ci] + arr[cj] + arr[ck]
        invariant forall a, b, c :: 0 <= a < b < c < n && a < i ==>
            AbsoluteDifference(arr[a] + arr[b] + arr[c], target) >= AbsoluteDifference(closest, target)
    {
        ghost var oldClosest := closest;
        closest, ci, cj, ck := twoPointerSearch(arr, i, target, closest, ci, cj, ck);

        // twoPointerSearch ensures: for all b, c with i < b < c < n,
        //   AbsoluteDiff(arr[i]+arr[b]+arr[c], target) >= AbsoluteDiff(closest, target)
        // And closest is at least as good as oldClosest
        // Combined with the outer invariant: for a < i, all triples with first element a are dominated

        // For the next iteration's invariant (a < i+1 = a <= i):
        // Case a < i: by old invariant and closest being at least as good
        // Case a == i: by twoPointerSearch postcondition

        i := i + 1;
    }

    assert i == n - 2;

    // For any valid triple (a, b, c), we have a <= n-3 < n-2 = i
    forall a, b, c | 0 <= a < b < c < n
      ensures AbsoluteDifference(arr[a] + arr[b] + arr[c], target) >= AbsoluteDifference(closest, target)
    {
      assert a < n - 2;
      assert a < i;
    }

    // Prove achievability in nums
    assert 0 <= ci < cj < ck < |arr[..]|;
    assert arr[..][ci] + arr[..][cj] + arr[..][ck] == closest;
    assert tripleAchievableOrdered(arr[..], closest);
    multisetTripleTransfer(arr[..], nums, closest);

    // Prove optimality in nums
    optimalityTransfer(arr[..], nums, closest, target);

    result := closest;
}
