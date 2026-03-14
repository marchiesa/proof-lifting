// Remove All Occurrences of Value from Array -- Test cases

method {:axiom} RemoveValue(a: seq<int>, val: int) returns (result: seq<int>)
  ensures forall i :: 0 <= i < |result| ==> result[i] != val
  ensures forall x :: x != val ==> multiset(result)[x] == multiset(a)[x]
  ensures forall i :: 0 <= i < |result| ==> result[i] in a

method TestRemove()
{
  var r := RemoveValue([1, 2, 3, 2, 1], 2);
  assert 2 !in r;
  assert multiset(r)[1] == multiset([1, 2, 3, 2, 1])[1] == 2;
}

method TestRemoveNotPresent()
{
  var r := RemoveValue([1, 2, 3], 5);
  assert multiset(r)[1] == 1;
  assert multiset(r)[2] == 1;
  assert multiset(r)[3] == 1;
}

method TestRemoveAll()
{
  var r := RemoveValue([7, 7, 7], 7);
  assert 7 !in r;
}

method TestEmpty()
{
  var r := RemoveValue([], 1);
  assert |r| >= 0;
}
