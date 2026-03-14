// Selection Sort
// Task: Add loop invariants so that Dafny can verify this program.

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
  {
    var minIdx := i;
    var j := i + 1;
    while j < a.Length
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
