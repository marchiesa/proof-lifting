// Median of Two Sorted Arrays -- Test cases
predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method {:axiom} MergeSorted(a: seq<int>, b: seq<int>) returns (merged: seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
  ensures |merged| == |a| + |b|
  ensures multiset(merged) == multiset(a) + multiset(b)
  ensures IsSorted(merged)

method TestMerge() {
  var r := MergeSorted([1, 3], [2]);
  assert |r| == 3;
}

method TestMergeEmpty() {
  var r := MergeSorted([], [1, 2, 3]);
  assert |r| == 3;
}

method TestMergeBothEmpty() {
  var r := MergeSorted([], []);
  assert |r| == 0;
}
