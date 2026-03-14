// Remove Duplicates from Sorted Sequence -- Reference solution with invariants

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate IsStrictlySorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

method RemoveDuplicates(a: seq<int>) returns (result: seq<int>)
  requires IsSorted(a)
  ensures IsStrictlySorted(result)
  ensures forall x :: x in multiset(result) ==> x in multiset(a)
  ensures forall x :: x in multiset(a) ==> x in multiset(result)
  ensures |result| <= |a|
{
  if |a| == 0 {
    return [];
  }
  result := [a[0]];
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant 1 <= |result| <= i
    invariant IsStrictlySorted(result)
    invariant result[|result| - 1] == a[i - 1]
    invariant forall x :: x in multiset(result) ==> x in multiset(a[..i])
    invariant forall x :: x in multiset(a[..i]) ==> x in multiset(result)
    decreases |a| - i
  {
    if a[i] != result[|result| - 1] {
      assert IsSorted(a);
      assert a[i] >= a[i - 1] == result[|result| - 1];
      assert a[i] > result[|result| - 1];
      result := result + [a[i]];
    }
    assert a[..i+1] == a[..i] + [a[i]];
    i := i + 1;
  }
  assert a[..i] == a;
}
