// Heap Sort (Selection Sort variant)
// Task: Add loop invariants so that Dafny can verify this program.
// Sort by repeatedly selecting the maximum and placing it at the end.

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
  {
    // Find max in a[0..end+1]
    var maxIdx := 0;
    var i := 1;
    while i <= end
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
