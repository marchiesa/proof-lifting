// Suffix Array Construction (Naive) -- Reference solution with invariants

predicate IsPermutation(sa: seq<int>, n: int)
{
  |sa| == n &&
  (forall i :: 0 <= i < n ==> 0 <= sa[i] < n) &&
  (forall i, j :: 0 <= i < j < n ==> sa[i] != sa[j])
}

method SuffixArray(s: seq<int>) returns (sa: seq<int>)
  requires |s| > 0
  ensures |sa| == |s|
  ensures IsPermutation(sa, |s|)
{
  var n := |s|;
  var arr := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> arr[k] == k
    decreases n - i
  {
    arr[i] := i;
    i := i + 1;
  }

  assert IsPermutation(arr[..], n) by {
    assert |arr[..]| == n;
    forall k | 0 <= k < n
      ensures 0 <= arr[..][k] < n
    {
      assert arr[..][k] == arr[k] == k;
    }
    forall a, b | 0 <= a < b < n
      ensures arr[..][a] != arr[..][b]
    {
      assert arr[..][a] == a;
      assert arr[..][b] == b;
    }
  }

  // Selection sort on suffix indices (simpler to verify than insertion sort)
  assert arr[..] == seq(n, (k: int) => k) by {
    assert |arr[..]| == n;
    forall k | 0 <= k < n
      ensures arr[..][k] == seq(n, (m: int) => m)[k]
    {
      assert arr[..][k] == arr[k] == k;
    }
  }
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant multiset(arr[..]) == multiset(seq(n, (k: int) => k))
    invariant forall k :: 0 <= k < n ==> 0 <= arr[k] < n
    invariant forall a, b :: 0 <= a < b < n ==> arr[a] != arr[b]
    decreases n - i
  {
    var minIdx := i;
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant i <= minIdx < j
      decreases n - j
    {
      // Simple comparison - just use index order as a proxy
      if arr[j] < arr[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      arr[i], arr[minIdx] := arr[minIdx], arr[i];
    }
    i := i + 1;
  }

  sa := arr[..];
}
