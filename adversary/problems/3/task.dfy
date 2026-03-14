// Problem 3: Sequence Slicing Pitfalls — Merge Sorted Halves
//
// Task: Add invariants and any needed assertions so this method verifies.
// Given a sequence that is sorted in its first half [0..m) and sorted in
// its second half [m..n), merge them into a fully sorted result.

predicate SortedSeq(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method MergeSorted(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires SortedSeq(a)
  requires SortedSeq(b)
  ensures SortedSeq(result)
  ensures |result| == |a| + |b|
  ensures multiset(result) == multiset(a) + multiset(b)
{
  result := [];
  var i := 0;
  var j := 0;
  while i < |a| || j < |b|
    // TODO: add invariants here
  {
    if i < |a| && (j >= |b| || a[i] <= b[j]) {
      result := result + [a[i]];
      i := i + 1;
    } else {
      result := result + [b[j]];
      j := j + 1;
    }
  }
}
