// Array Intersection of Two Sorted Arrays -- Test cases

predicate StrictlySorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

predicate IsSubsetOf(a: seq<int>, b: seq<int>)
{
  forall x :: x in a ==> x in b
}

method {:axiom} Intersection(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires StrictlySorted(a)
  requires StrictlySorted(b)
  ensures StrictlySorted(result)
  ensures IsSubsetOf(result, a)
  ensures IsSubsetOf(result, b)
  ensures forall x :: x in a && x in b ==> x in result

method TestBasic()
{
  var r := Intersection([1, 3, 5, 7], [2, 3, 5, 8]);
  assert 3 in r;
  assert 5 in r;
}

method TestNoOverlap()
{
  var r := Intersection([1, 3, 5], [2, 4, 6]);
  assert StrictlySorted(r);
}

method TestEmpty()
{
  var r := Intersection([], [1, 2, 3]);
  assert StrictlySorted(r);
}

method TestIdentical()
{
  var r := Intersection([1, 2, 3], [1, 2, 3]);
  assert 1 in r;
  assert 2 in r;
  assert 3 in r;
}
