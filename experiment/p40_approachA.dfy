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

lemma MultisetContainsImpliesSeqContains(s: seq<int>, v: int)
  requires v in multiset(s)
  ensures SeqContains(s, v)
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant v in multiset(s[i..])
  {
    if s[i] == v {
      return;
    }
    assert s[i..] == [s[i]] + s[i+1..];
    i := i + 1;
  }
}

lemma SeqContainsImpliesMultisetContains(s: seq<int>, v: int)
  requires SeqContains(s, v)
  ensures v in multiset(s)
{
  var i :| 0 <= i < |s| && s[i] == v;
}

lemma MultisetEqPreservesSeqContains(s1: seq<int>, s2: seq<int>, v: int)
  requires multiset(s1) == multiset(s2)
  ensures SeqContains(s1, v) == SeqContains(s2, v)
{
  if SeqContains(s1, v) {
    SeqContainsImpliesMultisetContains(s1, v);
    MultisetContainsImpliesSeqContains(s2, v);
  }
  if SeqContains(s2, v) {
    SeqContainsImpliesMultisetContains(s2, v);
    MultisetContainsImpliesSeqContains(s1, v);
  }
}

// Ghost function: set of indices where arr[j] == j+1
ghost function CorrectIndices(a: seq<int>): set<int>
{
  set j | 0 <= j < |a| && a[j] == j + 1
}

ghost function IndexSet(n: nat): set<int>
{
  set j {:autotriggers false} | 0 <= j < n
}

lemma CorrectIndicesBound(a: seq<int>)
  ensures |CorrectIndices(a)| <= |a|
{
  var indices := IndexSet(|a|);
  assert CorrectIndices(a) <= indices;
  CardinalitySubset(CorrectIndices(a), indices);
  IndexSetSize(|a|);
}

lemma IndexSetSize(n: nat)
  ensures |IndexSet(n)| == n
{
  if n == 0 {
  } else {
    assert IndexSet(n) == IndexSet(n - 1) + {n - 1};
    IndexSetSize(n - 1);
  }
}

lemma CardinalitySubset<T>(a: set<T>, b: set<T>)
  requires a <= b
  ensures |a| <= |b|
{
  if a == {} {
  } else {
    var x :| x in a;
    CardinalitySubset(a - {x}, b - {x});
  }
}

lemma StrictSupersetHasLargerCardinality<T>(a: set<T>, b: set<T>)
  requires a <= b
  requires a != b
  ensures |a| < |b|
{
  var x :| x in b && x !in a;
  assert a <= b - {x};
  CardinalitySubset(a, b - {x});
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
      invariant arr.Length == n
      invariant forall j :: 0 <= j < i ==> arr[j] == nums[j]
    {
        arr[i] := nums[i];
        i := i + 1;
    }

    assert arr[..] == nums;

    i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant arr.Length == n
      invariant multiset(arr[..]) == multiset(nums)
      invariant forall j :: 0 <= j < i ==>
        (arr[j] == j + 1 || arr[j] < 1 || arr[j] > n || arr[arr[j] - 1] == arr[j])
    {
        ghost var startCorrect := CorrectIndices(arr[..]);
        CorrectIndicesBound(arr[..]);
        while 1 <= arr[i] <= n && arr[arr[i] - 1] != arr[i]
          invariant arr.Length == n
          invariant 0 <= i < n
          invariant multiset(arr[..]) == multiset(nums)
          invariant forall j :: 0 <= j < i ==>
            (arr[j] == j + 1 || arr[j] < 1 || arr[j] > n || arr[arr[j] - 1] == arr[j])
          invariant startCorrect <= CorrectIndices(arr[..])
          decreases n - |CorrectIndices(arr[..])|
        {
            ghost var oldSeq := arr[..];
            ghost var oldCorrect := CorrectIndices(arr[..]);
            var target := arr[i] - 1;
            assert target != i;  // because arr[arr[i]-1] != arr[i] means arr[target] != arr[i]
                                 // if target == i then arr[target] == arr[i], contradiction
            assert oldSeq[target] != target + 1;  // arr[target] != arr[i] and arr[i] == target+1 would mean arr[target] != target+1
            // Actually: target = arr[i]-1, so target+1 = arr[i]. arr[target] != arr[i] means arr[target] != target+1.

            var temp := arr[target];
            arr[target] := arr[i];
            arr[i] := temp;

            assert arr[target] == target + 1;

            // Prove CorrectIndices grows
            ghost var newSeq := arr[..];
            assert target in CorrectIndices(newSeq);
            assert target !in oldCorrect;
            // For j != i and j != target, arr[j] unchanged
            assert forall j :: 0 <= j < n && j != i && j != target ==> newSeq[j] == oldSeq[j];
            // So any j in oldCorrect with j != i and j != target is still in CorrectIndices(newSeq)
            assert forall j :: j in oldCorrect && j != i && j != target ==> j in CorrectIndices(newSeq);
            // Even if i was in oldCorrect, we still gained target which wasn't
            // So |CorrectIndices(newSeq)| >= |oldCorrect - {i}| + 1 >= |oldCorrect|
            // Actually, we need |CorrectIndices(newSeq)| > |oldCorrect|
            // oldCorrect - {i} <= CorrectIndices(newSeq) (removing at most i)
            // target in CorrectIndices(newSeq) and target !in oldCorrect
            // So CorrectIndices(newSeq) >= (oldCorrect - {i}) + {target}
            // If i was not in oldCorrect: CorrectIndices(newSeq) >= oldCorrect + {target}, so size increased
            // If i was in oldCorrect: CorrectIndices(newSeq) >= (oldCorrect - {i}) + {target},
            //   and |oldCorrect - {i}| = |oldCorrect| - 1, so |(oldCorrect - {i}) + {target}| = |oldCorrect|
            //   But we might have gained even more. Hmm, this case is tricky.
            //   Wait, if i was in oldCorrect, then oldSeq[i] == i+1.
            //   After swap, arr[i] = temp = oldSeq[target].
            //   We need arr[i] != i+1 (i.e., we lost i from correct).
            //   But could arr[i] == i+1? That would mean temp == i+1, i.e., oldSeq[target] == i+1.
            //   But target = oldSeq[i] - 1 = (i+1) - 1 = i. So target == i. But we asserted target != i.
            //   Contradiction! So if i was in oldCorrect, target == i, which can't happen.
            //   Therefore i was NOT in oldCorrect.
            assert i !in oldCorrect by {
              if i in oldCorrect {
                assert oldSeq[i] == i + 1;
                assert target == oldSeq[i] - 1 == i;
                assert false;
              }
            }
            assert oldCorrect <= CorrectIndices(newSeq) by {
              forall j | j in oldCorrect
                ensures j in CorrectIndices(newSeq)
              {
                if j == target {
                  assert j in CorrectIndices(newSeq);
                } else if j == i {
                  assert false; // i !in oldCorrect
                } else {
                  assert newSeq[j] == oldSeq[j];
                  assert j in CorrectIndices(newSeq);
                }
              }
            }
            assert target in CorrectIndices(newSeq) && target !in oldCorrect;
            assert CorrectIndices(newSeq) >= oldCorrect + {target};
            // Prove |CorrectIndices(newSeq)| > |oldCorrect|
            StrictSupersetHasLargerCardinality(oldCorrect, CorrectIndices(newSeq));
            // Prove n - |CorrectIndices(newSeq)| >= 0
            CorrectIndicesBound(newSeq);
            assert startCorrect <= CorrectIndices(newSeq);
        }
        i := i + 1;
    }

    // Loop 3: find first missing positive
    i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant arr.Length == n
      invariant multiset(arr[..]) == multiset(nums)
      invariant forall j :: 0 <= j < i ==> arr[j] == j + 1
      invariant forall j :: 0 <= j < n ==>
        (arr[j] == j + 1 || arr[j] < 1 || arr[j] > n || arr[arr[j] - 1] == arr[j])
    {
        if arr[i] != i + 1 {
            assert !SeqContains(arr[..], i + 1) by {
              if SeqContains(arr[..], i + 1) {
                var k :| 0 <= k < |arr[..]| && arr[..][k] == i + 1;
                assert arr[k] == i + 1;
                assert k != i;
                assert 1 <= arr[k] <= n;
                assert arr[arr[k] - 1] == arr[k];
                assert arr[i] == i + 1;
                assert false;
              }
            }
            MultisetEqPreservesSeqContains(arr[..], nums, i + 1);

            assert forall x :: 1 <= x <= i ==> SeqContains(nums, x) by {
              forall x | 1 <= x <= i
                ensures SeqContains(nums, x)
              {
                assert arr[x - 1] == x;
                assert arr[..][x - 1] == x;
                assert SeqContains(arr[..], x);
                MultisetEqPreservesSeqContains(arr[..], nums, x);
              }
            }
            return i + 1;
        }
        i := i + 1;
    }

    assert forall x :: 1 <= x <= n ==> SeqContains(nums, x) by {
      forall x | 1 <= x <= n
        ensures SeqContains(nums, x)
      {
        assert arr[x - 1] == x;
        assert arr[..][x - 1] == x;
        assert SeqContains(arr[..], x);
        MultisetEqPreservesSeqContains(arr[..], nums, x);
      }
    }

    assert !SeqContains(nums, n + 1) by {
      if SeqContains(nums, n + 1) {
        SeqContainsImpliesMultisetContains(nums, n + 1);
        assert n + 1 in multiset(arr[..]);
        MultisetContainsImpliesSeqContains(arr[..], n + 1);
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
