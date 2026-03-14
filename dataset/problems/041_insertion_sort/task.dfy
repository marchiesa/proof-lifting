// Insertion Sort
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method InsertionSort(a: array<int>)
  modifies a
  ensures IsSorted(a[..])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var i := 1;
  while i < a.Length
  {
    var key := a[i];
    var j := i - 1;
    while j >= 0 && a[j] > key
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    a[j + 1] := key;
    i := i + 1;
  }
}
