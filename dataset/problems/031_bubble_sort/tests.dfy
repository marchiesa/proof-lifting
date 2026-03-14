// Bubble Sort -- Test cases

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method {:axiom} BubbleSort(a: array<int>)
  modifies a
  ensures IsSorted(a[..])
  ensures multiset(a[..]) == old(multiset(a[..]))

method TestBasic()
{
  var a := new int[] [3, 1, 4, 1, 5];
  var old_ms := multiset(a[..]);
  BubbleSort(a);
  assert IsSorted(a[..]);
  assert multiset(a[..]) == old_ms;
}

method TestAlreadySorted()
{
  var a := new int[] [1, 2, 3, 4, 5];
  BubbleSort(a);
  assert IsSorted(a[..]);
}

method TestReversed()
{
  var a := new int[] [5, 4, 3, 2, 1];
  BubbleSort(a);
  assert IsSorted(a[..]);
}

method TestEmpty()
{
  var a := new int[] [];
  BubbleSort(a);
  assert IsSorted(a[..]);
}

method TestSingleElement()
{
  var a := new int[] [42];
  BubbleSort(a);
  assert IsSorted(a[..]);
}
