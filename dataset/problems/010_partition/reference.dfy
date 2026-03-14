// Partition Around Pivot -- Reference solution with invariants

method Partition(a: seq<int>, pivot: int) returns (result: seq<int>, splitIdx: int)
  ensures |result| == |a|
  ensures 0 <= splitIdx <= |a|
  ensures forall i :: 0 <= i < splitIdx ==> result[i] <= pivot
  ensures forall i :: splitIdx <= i < |result| ==> result[i] > pivot
  ensures multiset(result) == multiset(a)
{
  var lo: seq<int> := [];
  var hi: seq<int> := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < |lo| ==> lo[j] <= pivot
    invariant forall j :: 0 <= j < |hi| ==> hi[j] > pivot
    invariant |lo| + |hi| == i
    invariant multiset(lo) + multiset(hi) == multiset(a[..i])
    decreases |a| - i
  {
    if a[i] <= pivot {
      lo := lo + [a[i]];
    } else {
      hi := hi + [a[i]];
    }
    assert a[..i+1] == a[..i] + [a[i]];
    i := i + 1;
  }
  assert a[..i] == a;
  result := lo + hi;
  splitIdx := |lo|;
}
