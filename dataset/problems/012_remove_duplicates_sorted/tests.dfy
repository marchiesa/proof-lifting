// Remove Duplicates from Sorted Sequence -- Test cases

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate IsStrictlySorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

method {:axiom} RemoveDuplicates(a: seq<int>) returns (result: seq<int>)
  requires IsSorted(a)
  ensures IsStrictlySorted(result)
  ensures forall x :: x in multiset(result) ==> x in multiset(a)
  ensures forall x :: x in multiset(a) ==> x in multiset(result)
  ensures |result| <= |a|

method TestWithDuplicates()
{
  var a := [1, 1, 2, 3, 3, 3, 4];
  var r := RemoveDuplicates(a);
  assert IsStrictlySorted(r);
  // 1 is in a, so must be in result
  assert 1 in multiset(a);
  assert 1 in multiset(r);
  // 4 is in a, so must be in result
  assert 4 in multiset(a);
  assert 4 in multiset(r);
}

method TestNoDuplicates()
{
  var a := [1, 2, 3];
  var r := RemoveDuplicates(a);
  assert 1 in multiset(a);
  assert 1 in multiset(r);
  assert 3 in multiset(a);
  assert 3 in multiset(r);
}

method TestEmpty()
{
  var a: seq<int> := [];
  var r := RemoveDuplicates(a);
  assert |r| <= |a|;
  assert |r| == 0;
}

method TestAllSame()
{
  var a := [5, 5, 5];
  var r := RemoveDuplicates(a);
  assert 5 in multiset(a);
  assert 5 in multiset(r);
  assert |r| <= |a|;
}
