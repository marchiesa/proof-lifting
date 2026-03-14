// Remove Duplicates from Sorted Array -- Test cases

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate StrictlySorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

method {:axiom} RemoveDuplicates(a: array<int>) returns (k: nat)
  requires IsSorted(a[..])
  modifies a
  ensures k <= a.Length
  ensures StrictlySorted(a[..k])
  ensures forall i :: 0 <= i < k ==> a[i] in old(a[..])
  ensures forall j :: 0 <= j < |old(a[..])| ==> exists i :: 0 <= i < k && a[i] == old(a[..])[j]

method TestWithDuplicates()
{
  var a := new int[] [1, 1, 2, 2, 3];
  var k := RemoveDuplicates(a);
  assert StrictlySorted(a[..k]);
}

method TestNoDuplicates()
{
  var a := new int[] [1, 2, 3];
  var k := RemoveDuplicates(a);
  assert StrictlySorted(a[..k]);
}

method TestSingleElement()
{
  var a := new int[] [5];
  var k := RemoveDuplicates(a);
  assert StrictlySorted(a[..k]);
  assert k >= 1;
}

method TestAllSame()
{
  var a := new int[] [3, 3, 3, 3];
  var k := RemoveDuplicates(a);
  assert StrictlySorted(a[..k]);
}
