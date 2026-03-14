// Merge Sort -- Test cases

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method {:axiom} MergeSort(s: seq<int>) returns (r: seq<int>)
  ensures IsSorted(r)
  ensures multiset(r) == multiset(s)

method TestBasic()
{
  var r := MergeSort([3, 1, 4, 1, 5]);
  assert IsSorted(r);
  assert multiset(r) == multiset([3, 1, 4, 1, 5]);
}

method TestEmpty()
{
  var r := MergeSort([]);
  assert |r| == 0;
}

method TestSingle()
{
  var r := MergeSort([42]);
  assert r == [42];
}

method TestAlreadySorted()
{
  var r := MergeSort([1, 2, 3]);
  assert IsSorted(r);
}
