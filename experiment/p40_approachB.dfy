function SeqContains(s: seq<int>, v: int): bool
{
  exists i:int :: 0 <= i < |s| && s[i] == v
}

predicate firstMissingPositivePost(nums: seq<int>, result: int)
{
  result > 0
  && !SeqContains(nums, result)
  && (forall x:int :: 1 <= x < result ==> SeqContains(nums, x))
}

lemma MultisetContainsEquiv(arr: array<int>, nums: seq<int>, v: int)
  requires multiset(arr[..]) == multiset(nums)
  ensures SeqContains(arr[..], v) <==> SeqContains(nums, v)
{
  var s := arr[..];
  if SeqContains(s, v) {
    var k :| 0 <= k < |s| && s[k] == v;
    assert v in multiset(s);
    assert v in multiset(nums);
    MultisetMemberImpliesSeqContains(nums, v);
  }
  if SeqContains(nums, v) {
    var k :| 0 <= k < |nums| && nums[k] == v;
    assert v in multiset(nums);
    assert v in multiset(s);
    MultisetMemberImpliesSeqContains(s, v);
  }
}

lemma MultisetMemberImpliesSeqContains(s: seq<int>, v: int)
  requires v in multiset(s)
  ensures SeqContains(s, v)
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> s[j] != v
  {
    if s[i] == v {
      return;
    }
    i := i + 1;
  }
  assert multiset(s)[v] == 0;
  assert false;
}

// Count fixed points: positions k in [0,n) where a[k] == k+1
function CountFixed(a: seq<int>, n: int): nat
  requires 0 <= n <= |a|
{
  if n == 0 then 0
  else (if a[n-1] == n then 1 else 0) + CountFixed(a, n-1)
}

lemma CountFixedUpperBound(a: seq<int>, n: int)
  requires 0 <= n <= |a|
  ensures CountFixed(a, n) <= n
{
  if n > 0 {
    CountFixedUpperBound(a, n - 1);
  }
}

// If we change position p and nothing else, and p was not fixed and becomes fixed,
// then CountFixed increases by 1 for those positions, and doesn't change for others.
lemma CountFixedSwapEffect(a: seq<int>, b: seq<int>, n: int, p: int, q: int)
  requires |a| == n && |b| == n && 0 <= n
  requires 0 <= p < n && 0 <= q < n && p != q
  requires a[p] != p + 1  // p was not fixed in a
  requires a[q] != q + 1  // q was not fixed in a
  requires b[p] == p + 1  // p is fixed in b
  requires forall k :: 0 <= k < n && k != p && k != q ==> b[k] == a[k]
  ensures CountFixed(b, n) >= CountFixed(a, n) + 1
{
  CountFixedSwapHelper(a, b, n, p, q);
}

lemma CountFixedSwapHelper(a: seq<int>, b: seq<int>, m: int, p: int, q: int)
  requires |a| == |b| && 0 <= m <= |a|
  requires 0 <= p < |a| && 0 <= q < |a| && p != q
  requires a[p] != p + 1
  requires a[q] != q + 1
  requires b[p] == p + 1
  requires forall k :: 0 <= k < |a| && k != p && k != q ==> b[k] == a[k]
  ensures CountFixed(b, m) >= CountFixed(a, m) + (if p < m then 1 else 0)
  decreases m
{
  if m == 0 {
  } else {
    CountFixedSwapHelper(a, b, m - 1, p, q);
    var pos := m - 1;
    if pos == p {
      // b[p] == p + 1 so b contributes 1, a[p] != p+1 so a contributes 0
      assert (if b[pos] == pos + 1 then 1 else 0) == 1;
      assert (if a[pos] == pos + 1 then 1 else 0) == 0;
    } else if pos == q {
      // q might or might not be fixed in b, but wasn't fixed in a
      assert (if a[pos] == pos + 1 then 1 else 0) == 0;
      // b[q] >= a[q] contribution-wise (a was 0, b is 0 or 1)
    } else {
      // b[pos] == a[pos], same contribution
      assert b[pos] == a[pos];
    }
  }
}

method firstMissingPositive(nums: seq<int>) returns (result: int)
  requires |nums| >= 1
  ensures  firstMissingPositivePost(nums, result)
{
    var n := |nums|;
    var arr := new int[n];
    var i := 0;

    while i < n
      invariant 0 <= i <= n
      invariant forall j :: 0 <= j < i ==> arr[j] == nums[j]
    {
        arr[i] := nums[i];
        i := i + 1;
    }

    assert arr[..] == nums;
    assert multiset(arr[..]) == multiset(nums);

    // Phase 2: Cycle sort - place each value v at position v-1
    i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant multiset(arr[..]) == multiset(nums)
      invariant forall j :: 0 <= j < i ==> (1 <= arr[j] <= n ==> arr[arr[j]-1] == arr[j])
      decreases n - i
    {
        CountFixedUpperBound(arr[..], n);
        while 1 <= arr[i] <= n && arr[arr[i] - 1] != arr[i]
          invariant 0 <= i < n
          invariant multiset(arr[..]) == multiset(nums)
          invariant 1 <= arr[i] <= n ==> 0 <= arr[i] - 1 < n
          invariant forall j :: 0 <= j < i ==> (1 <= arr[j] <= n ==> arr[arr[j]-1] == arr[j])
          invariant CountFixed(arr[..], n) <= n
          decreases n - CountFixed(arr[..], n)
        {
            ghost var old_snap := arr[..];
            ghost var old_count := CountFixed(old_snap, n);

            var target := arr[i] - 1;
            assert target != i by {
              if target == i {
                assert arr[arr[i] - 1] == arr[i];
              }
            }
            // Before swap facts
            assert old_snap[target] != target + 1 by {
              // arr[target] != arr[i] (loop condition) and arr[i] = target + 1
              assert old_snap[target] != old_snap[i];
              assert old_snap[i] == target + 1;
            }
            assert old_snap[i] != i + 1 by {
              assert old_snap[i] == target + 1;
              assert target != i;
            }

            var temp := arr[target];
            arr[target] := arr[i];
            arr[i] := temp;

            ghost var new_snap := arr[..];

            // Prove the relationship between new_snap and old_snap
            assert new_snap[target] == old_snap[i];
            assert new_snap[i] == old_snap[target];
            assert forall k :: 0 <= k < n && k != i && k != target ==> new_snap[k] == old_snap[k];
            assert new_snap[target] == target + 1;

            CountFixedSwapEffect(old_snap, new_snap, n, target, i);
            CountFixedUpperBound(new_snap, n);
        }
        i := i + 1;
    }

    // Phase 3: Find first missing positive
    i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant multiset(arr[..]) == multiset(nums)
      invariant forall j :: 0 <= j < i ==> arr[j] == j + 1
      decreases n - i
    {
        if arr[i] != i + 1 {
            assert forall j :: 0 <= j < n ==> (1 <= arr[j] <= n ==> arr[arr[j]-1] == arr[j]);
            assert !SeqContains(arr[..], i + 1) by {
              if SeqContains(arr[..], i + 1) {
                var k :| 0 <= k < |arr[..]| && arr[..][k] == i + 1;
                assert arr[k] == i + 1;
                assert 1 <= arr[k] <= n;
                assert arr[arr[k] - 1] == arr[k];
                assert arr[i] == i + 1;
                assert false;
              }
            }
            MultisetContainsEquiv(arr, nums, i + 1);

            forall x | 1 <= x < i + 1
              ensures SeqContains(nums, x)
            {
              assert arr[x - 1] == x;
              assert 0 <= x - 1 < |arr[..]| && arr[..][x-1] == x;
              assert SeqContains(arr[..], x);
              MultisetContainsEquiv(arr, nums, x);
            }

            return i + 1;
        }
        i := i + 1;
    }

    assert forall j :: 0 <= j < n ==> arr[j] == j + 1;
    forall x | 1 <= x <= n
      ensures SeqContains(nums, x)
    {
      assert arr[x-1] == x;
      assert 0 <= x - 1 < |arr[..]| && arr[..][x-1] == x;
      assert SeqContains(arr[..], x);
      MultisetContainsEquiv(arr, nums, x);
    }

    assert !SeqContains(nums, n + 1) by {
      if SeqContains(nums, n + 1) {
        MultisetContainsEquiv(arr, nums, n + 1);
        assert SeqContains(arr[..], n + 1);
        var k :| 0 <= k < |arr[..]| && arr[..][k] == n + 1;
        assert arr[k] == n + 1;
        assert arr[k] == k + 1;
        assert k == n;
        assert k < n;
        assert false;
      }
    }

    return n + 1;
}
