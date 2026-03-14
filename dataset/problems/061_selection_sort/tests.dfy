// Selection Sort -- Test cases

predicate Sorted(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  forall i, j :: lo <= i < j < hi ==> a[i] <= a[j]
}

method {:axiom} SelectionSort(a: array<int>)
  modifies a
  ensures Sorted(a, 0, a.Length)
  ensures multiset(a[..]) == old(multiset(a[..]))

method TestBasic()
{
  var a := new int[] [3, 1, 2];
  var old_ms := multiset(a[..]);
  SelectionSort(a);
  assert Sorted(a, 0, a.Length);
  assert multiset(a[..]) == old_ms;
}

method TestAlreadySorted()
{
  var a := new int[] [1, 2, 3, 4, 5];
  var old_ms := multiset(a[..]);
  SelectionSort(a);
  assert Sorted(a, 0, a.Length);
  assert multiset(a[..]) == old_ms;
}

method TestReverseSorted()
{
  var a := new int[] [5, 4, 3, 2, 1];
  var old_ms := multiset(a[..]);
  SelectionSort(a);
  assert Sorted(a, 0, a.Length);
  assert multiset(a[..]) == old_ms;
}

method TestSingleElement()
{
  var a := new int[] [42];
  var old_ms := multiset(a[..]);
  SelectionSort(a);
  assert Sorted(a, 0, a.Length);
  assert multiset(a[..]) == old_ms;
}
