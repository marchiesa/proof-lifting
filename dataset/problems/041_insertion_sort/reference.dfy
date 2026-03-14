// Insertion Sort -- Reference solution with invariants

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// Helper: inserting key at position j+1 in a sorted prefix preserves multiset
lemma InsertPreservesMultiset(a: array<int>, old_a: seq<int>, j: int, i: int, key: int)
  requires a.Length == |old_a|
  requires 0 <= j + 1 <= i < a.Length
  requires forall p :: 0 <= p <= j ==> a[p] == old_a[p]
  requires a[j + 1] == key
  requires forall p :: j + 2 <= p <= i ==> a[p] == old_a[p - 1]
  requires forall p :: i + 1 <= p < a.Length ==> a[p] == old_a[p]
  requires key == old_a[i]
  ensures multiset(a[..]) == multiset(old_a)
{
  // The array a is old_a with old_a[i] removed and inserted at position j+1
  // Elements 0..j are same, j+1 is key, j+2..i are shifted right by 1, i+1.. are same
  assert a[..] == old_a[..j+1] + [key] + old_a[j+1..i] + old_a[i+1..] by {
    assert |a[..]| == |old_a[..j+1] + [key] + old_a[j+1..i] + old_a[i+1..]|;
    forall p | 0 <= p < a.Length
      ensures a[..][p] == (old_a[..j+1] + [key] + old_a[j+1..i] + old_a[i+1..])[p]
    {
    }
  }
  assert old_a == old_a[..j+1] + old_a[j+1..i] + [old_a[i]] + old_a[i+1..] by {
    assert old_a[..j+1] + old_a[j+1..] == old_a;
    assert old_a[j+1..] == old_a[j+1..i] + old_a[i..];
    assert old_a[i..] == [old_a[i]] + old_a[i+1..];
  }
}

method InsertionSort(a: array<int>)
  modifies a
  ensures IsSorted(a[..])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  if a.Length <= 1 { return; }
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant IsSorted(a[..i])
    invariant multiset(a[..]) == old(multiset(a[..]))
    decreases a.Length - i
  {
    var key := a[i];
    var j := i - 1;
    ghost var old_a := a[..];
    while j >= 0 && a[j] > key
      invariant -1 <= j <= i - 1
      invariant forall p :: 0 <= p <= j ==> a[p] == old_a[p]
      invariant forall p :: j + 2 <= p <= i ==> a[p] == old_a[p - 1]
      invariant forall p :: i + 1 <= p < a.Length ==> a[p] == old_a[p]
      invariant key == old_a[i]
      invariant IsSorted(a[..j+1])
      invariant forall p :: j + 2 <= p <= i ==> a[p] > key
      decreases j + 1
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    a[j + 1] := key;
    InsertPreservesMultiset(a, old_a, j, i, key);
    assert IsSorted(a[..i+1]);
    i := i + 1;
  }
  assert a[..a.Length] == a[..];
}
