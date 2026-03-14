// Median of Two Sorted Arrays -- Reference solution with invariants

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method MergeSorted(a: seq<int>, b: seq<int>) returns (merged: seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
  ensures |merged| == |a| + |b|
  ensures multiset(merged) == multiset(a) + multiset(b)
  ensures IsSorted(merged)
{
  merged := [];
  var i := 0;
  var j := 0;
  while i < |a| || j < |b|
    invariant 0 <= i <= |a|
    invariant 0 <= j <= |b|
    invariant |merged| == i + j
    invariant multiset(merged) == multiset(a[..i]) + multiset(b[..j])
    invariant IsSorted(merged)
    invariant |merged| > 0 && i < |a| ==> merged[|merged|-1] <= a[i]
    invariant |merged| > 0 && j < |b| ==> merged[|merged|-1] <= b[j]
    decreases |a| + |b| - i - j
  {
    if i < |a| && (j >= |b| || a[i] <= b[j]) {
      assert a[..i+1] == a[..i] + [a[i]];
      merged := merged + [a[i]];
      i := i + 1;
    } else {
      assert b[..j+1] == b[..j] + [b[j]];
      merged := merged + [b[j]];
      j := j + 1;
    }
  }
  assert a[..|a|] == a;
  assert b[..|b|] == b;
}
