// Three-Way Partition -- Reference solution with invariants

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
    invariant 0 <= lo <= mid <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] < pivot
    invariant forall i :: lo <= i < mid ==> a[i] == pivot
    invariant forall i :: hi <= i < a.Length ==> a[i] > pivot
    invariant multiset(a[..]) == old(multiset(a[..]))
    decreases hi - mid
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
