// Bubble Sort -- Reference solution with invariants

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method BubbleSort(a: array<int>)
  modifies a
  ensures IsSorted(a[..])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall p, q :: 0 <= p < i && i <= q < n ==> a[p] <= a[q]
    invariant IsSorted(a[..i])
    invariant multiset(a[..]) == old(multiset(a[..]))
    decreases n - i
  {
    var j := n - 1;
    while j > i
      invariant i <= j < n
      invariant forall p, q :: 0 <= p < i && i <= q < n ==> a[p] <= a[q]
      invariant IsSorted(a[..i])
      invariant forall k :: j < k < n ==> a[j] <= a[k]
      invariant multiset(a[..]) == old(multiset(a[..]))
      decreases j - i
    {
      if a[j - 1] > a[j] {
        a[j - 1], a[j] := a[j], a[j - 1];
      }
      j := j - 1;
    }
    // After inner loop: a[i] is the minimum of a[i..n]
    assert forall k :: i < k < n ==> a[i] <= a[k];
    i := i + 1;
  }
}
