// Merge Two Sorted Sequences -- Reference solution with invariants

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method MergeSorted(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
  ensures IsSorted(result)
  ensures |result| == |a| + |b|
  ensures multiset(result) == multiset(a) + multiset(b)
{
  result := [];
  var i := 0;
  var j := 0;
  while i < |a| || j < |b|
    invariant 0 <= i <= |a|
    invariant 0 <= j <= |b|
    invariant |result| == i + j
    invariant IsSorted(result)
    invariant multiset(result) == multiset(a[..i]) + multiset(b[..j])
    invariant |result| > 0 && i < |a| ==> result[|result| - 1] <= a[i]
    invariant |result| > 0 && j < |b| ==> result[|result| - 1] <= b[j]
    decreases |a| - i + |b| - j
  {
    if i < |a| && (j >= |b| || a[i] <= b[j]) {
      result := result + [a[i]];
      assert a[..i+1] == a[..i] + [a[i]];
      i := i + 1;
    } else {
      result := result + [b[j]];
      assert b[..j+1] == b[..j] + [b[j]];
      j := j + 1;
    }
  }
  assert a[..i] == a;
  assert b[..j] == b;
}
