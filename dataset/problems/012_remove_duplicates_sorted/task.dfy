// Remove Duplicates from Sorted Sequence
// Task: Add loop invariants so that Dafny can verify this program.

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
  {
    if a[i] != result[|result| - 1] {
      result := result + [a[i]];
    }
    i := i + 1;
  }
}
