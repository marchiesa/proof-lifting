// Linear Search -- Test cases

method {:axiom} LinearSearch(a: seq<int>, threshold: int) returns (index: int)
  ensures index == -1 ==> forall k :: 0 <= k < |a| ==> a[k] <= threshold
  ensures 0 <= index < |a| ==> a[index] > threshold
  ensures 0 <= index < |a| ==> forall j :: 0 <= j < index ==> a[j] <= threshold
  ensures index < 0 ==> index == -1

method TestFoundMiddle()
{
  var a := [1, 3, 5, 7];
  var idx := LinearSearch(a, 4);
  // a[2] == 5 > 4, so idx can't be -1
  if idx == -1 {
    assert a[2] <= 4;  // contradiction
  }
  assert idx != -1;
  assert idx >= 0;
}

method TestNotFound()
{
  var a := [1, 2, 3];
  var idx := LinearSearch(a, 10);
  if 0 <= idx < |a| {
    assert a[idx] > 10;
  }
}

method TestEmpty()
{
  var a: seq<int> := [];
  var idx := LinearSearch(a, 0);
  assert !(0 <= idx < |a|);
}

method TestFoundFirst()
{
  var a := [5, 1, 2];
  var idx := LinearSearch(a, 0);
  if idx == -1 {
    assert a[0] <= 0;  // contradiction: a[0] == 5
  }
  assert idx != -1;
  assert idx >= 0;
  // idx must be 0 since a[0] > 0 and postcondition says no earlier element satisfies
}
