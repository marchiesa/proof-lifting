// Three-Way Partition
// Task: Add loop invariants so that Dafny can verify this program.
// Partition array into elements < pivot, == pivot, > pivot.

method ThreeWayPartition(a: array<int>, pivot: int)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length && a[i] > pivot ==> a[j] >= pivot
  ensures forall i, j :: 0 <= i < j < a.Length && a[j] < pivot ==> a[i] <= pivot
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var lo := 0;
  var mid := 0;
  var hi := a.Length;
  while mid < hi
  {
    if a[mid] < pivot {
      a[lo], a[mid] := a[mid], a[lo];
      lo := lo + 1;
      mid := mid + 1;
    } else if a[mid] == pivot {
      mid := mid + 1;
    } else {
      hi := hi - 1;
      a[mid], a[hi] := a[hi], a[mid];
    }
  }
}
