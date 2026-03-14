// Selection Sort -- Reference solution with invariants

predicate Sorted(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  forall i, j :: lo <= i < j < hi ==> a[i] <= a[j]
}

method SelectionSort(a: array<int>)
  modifies a
  ensures Sorted(a, 0, a.Length)
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant Sorted(a, 0, i)
    invariant forall x, y :: 0 <= x < i <= y < a.Length ==> a[x] <= a[y]
    invariant multiset(a[..]) == old(multiset(a[..]))
    decreases a.Length - i
  {
    var minIdx := i;
    var j := i + 1;
    while j < a.Length
      invariant i <= minIdx < j <= a.Length
      invariant forall k :: i <= k < j ==> a[minIdx] <= a[k]
      invariant multiset(a[..]) == old(multiset(a[..]))
      decreases a.Length - j
    {
      if a[j] < a[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    a[i], a[minIdx] := a[minIdx], a[i];
    i := i + 1;
  }
}
