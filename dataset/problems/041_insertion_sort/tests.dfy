// Insertion Sort -- Test cases

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method {:axiom} InsertionSort(a: array<int>)
  modifies a
  ensures IsSorted(a[..])
  ensures multiset(a[..]) == old(multiset(a[..]))

method TestBasic()
{
  var a := new int[] [5, 3, 1, 4, 2];
  var old_ms := multiset(a[..]);
  InsertionSort(a);
  assert IsSorted(a[..]);
  assert multiset(a[..]) == old_ms;
}

method TestAlreadySorted()
{
  var a := new int[] [1, 2, 3, 4];
  InsertionSort(a);
  assert IsSorted(a[..]);
}

method TestReverse()
{
  var a := new int[] [4, 3, 2, 1];
  InsertionSort(a);
  assert IsSorted(a[..]);
}

method TestSingle()
{
  var a := new int[] [42];
  InsertionSort(a);
  assert IsSorted(a[..]);
}

method TestEmpty()
{
  var a := new int[] [];
  InsertionSort(a);
  assert IsSorted(a[..]);
}
