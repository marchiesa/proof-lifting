// Median of Two Sorted Arrays
// Task: Add loop invariants so that Dafny can verify this program.
// Merge two sorted arrays and return the middle element(s).

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// Merge specification
function MergeSpec(a: seq<int>, b: seq<int>): seq<int>
{
  if |a| == 0 then b
  else if |b| == 0 then a
  else if a[0] <= b[0] then [a[0]] + MergeSpec(a[1..], b)
  else [b[0]] + MergeSpec(a, b[1..])
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
  {
    if i < |a| && (j >= |b| || a[i] <= b[j]) {
      merged := merged + [a[i]];
      i := i + 1;
    } else {
      merged := merged + [b[j]];
      j := j + 1;
    }
  }
}
