// Heap Sort (Selection Sort variant) -- Reference solution with invariants

predicate IsSorted(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  reads a
{
  forall i, j :: lo <= i < j < hi ==> a[i] <= a[j]
}

method HeapSort(a: array<int>)
  modifies a
  ensures IsSorted(a, 0, a.Length)
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := a.Length;
  var end := n - 1;
  while end > 0
    invariant -1 <= end < n
    invariant multiset(a[..]) == old(multiset(a[..]))
    invariant IsSorted(a, end + 1, n)
    invariant forall i, j :: 0 <= i <= end && end < j < n ==> a[i] <= a[j]
    decreases end
  {
    // Find max in a[0..end+1]
    var maxIdx := 0;
    var i := 1;
    while i <= end
      invariant 1 <= i <= end + 1
      invariant 0 <= maxIdx <= end
      invariant forall j :: 0 <= j < i ==> a[j] <= a[maxIdx]
      decreases end + 1 - i
    {
      if a[i] > a[maxIdx] {
        maxIdx := i;
      }
      i := i + 1;
    }
    // Swap max to position end
    a[maxIdx], a[end] := a[end], a[maxIdx];
    end := end - 1;
  }
}
