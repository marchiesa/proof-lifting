// Find Missing Number -- Reference solution with invariants

predicate AllInRange(a: seq<int>, n: int)
{
  forall i :: 0 <= i < |a| ==> 0 <= a[i] <= n
}

predicate AllDistinct(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j]
}

predicate Contains(a: seq<int>, v: int)
{
  exists i :: 0 <= i < |a| && a[i] == v
}

// Pigeonhole: if n distinct values from [0..n] all appear in seq of length n,
// that's n+1 values in n slots - impossible.
// We prove: if all of 0..m-1 are in a, and |a|==n < m, contradiction.
lemma {:induction false} PigeonholeHelper(a: seq<int>, n: int, m: int)
  requires n >= 0
  requires |a| == n
  requires AllInRange(a, n)
  requires AllDistinct(a)
  requires m == n + 1
  requires forall v :: 0 <= v < m ==> Contains(a, v)
  ensures false
{
  // We have n+1 values each witnessed by some index in [0..n).
  // By pigeonhole two values share an index, contradicting AllDistinct.
  // Dafny can verify this with the right instantiation.
  assert Contains(a, n);
  var idx :| 0 <= idx < |a| && a[idx] == n;
  // Remove element at idx
  var a' := a[..idx] + a[idx+1..];
  assert |a'| == n - 1;
  // Each value v in 0..n-1 had a witness j != idx in a
  // so it still has a witness in a'
  forall v | 0 <= v < n
    ensures Contains(a', v)
  {
    assert Contains(a, v);
    var j :| 0 <= j < |a| && a[j] == v;
    assert j != idx; // because a[idx] == n != v
    if j < idx {
      assert 0 <= j < |a'| && a'[j] == v;
    } else {
      assert 0 <= j - 1 < |a'| && a'[j-1] == v;
    }
  }
  // Now a' has n-1 elements, all distinct, in range [0..n-1], containing all of 0..n-1
  if n > 1 {
    assert AllInRange(a', n - 1);
    assert AllDistinct(a');
    PigeonholeHelper(a', n - 1, n);
  } else {
    // n == 1, |a'| == 0, but Contains(a', 0) is required - contradiction
    assert Contains(a', 0);
    var j :| 0 <= j < |a'| && a'[j] == 0;
    assert |a'| == 0;
  }
}

method FindMissing(a: seq<int>, n: int) returns (missing: int)
  requires n >= 0
  requires |a| == n
  requires AllInRange(a, n)
  requires AllDistinct(a)
  ensures 0 <= missing <= n
  ensures !Contains(a, missing)
{
  var m := 0;
  while m <= n
    invariant 0 <= m <= n + 1
    invariant forall v :: 0 <= v < m ==> Contains(a, v)
    decreases n + 1 - m
  {
    var found := false;
    var i := 0;
    while i < |a|
      invariant 0 <= i <= |a|
      invariant found <==> Contains(a[..i], m)
      decreases |a| - i
    {
      if a[i] == m {
        found := true;
      }
      i := i + 1;
    }
    assert a[..i] == a;
    if !found {
      return m;
    }
    m := m + 1;
  }
  PigeonholeHelper(a, n, n + 1);
  return 0;
}
