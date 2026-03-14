// Merge Two Sorted Sequences
// Task: Add loop invariants so that Dafny can verify this program.

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
