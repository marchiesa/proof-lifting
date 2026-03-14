// Binary Search -- Test cases

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method {:axiom} BinarySearch(a: seq<int>, target: int) returns (index: int)
  requires IsSorted(a)
  ensures index == -1 ==> forall k :: 0 <= k < |a| ==> a[k] != target
  ensures 0 <= index < |a| ==> a[index] == target
  ensures index < 0 ==> index == -1

method TestFoundElement()
{
  var a := [1, 3, 5, 7, 9];
  var idx := BinarySearch(a, 5);
  // From postcondition: if idx == -1, all elements != 5
  // But a[2] == 5, so idx cannot be -1
  if idx == -1 {
    assert a[2] != 5;  // contradiction: a[2] is 5
  }
  assert idx != -1;
  // From ensures index < 0 ==> index == -1, contrapositive: idx != -1 ==> idx >= 0
  assert idx >= 0;
}

method TestNotFoundElement()
{
  var a := [1, 3, 5, 7, 9];
  var idx := BinarySearch(a, 4);
  // The postcondition guarantees: if 0 <= idx < |a|, then a[idx] == 4
  // We test the postcondition holds (whatever idx is)
  if 0 <= idx < |a| {
    assert a[idx] == 4;
  }
}

method TestEmpty()
{
  var a: seq<int> := [];
  var idx := BinarySearch(a, 42);
  // |a| == 0, so idx can't be a valid index
  // If idx >= 0, then 0 <= idx < |a| must hold, but |a| == 0
  // So idx must be negative, and from the spec, idx < 0 ==> idx == -1
  assert !(0 <= idx < |a|);
}

method TestSingleElementFound()
{
  var a := [42];
  var idx := BinarySearch(a, 42);
  if idx == -1 {
    assert a[0] != 42;  // contradiction
  }
  assert idx != -1;
  assert idx >= 0;
}

method TestSingleElementNotFound()
{
  var a := [42];
  var idx := BinarySearch(a, 7);
  if 0 <= idx < |a| {
    assert a[idx] == 7;
  }
}
