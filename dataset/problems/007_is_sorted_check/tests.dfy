// Is Sorted Check -- Test cases

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method {:axiom} IsSortedCheck(a: seq<int>) returns (sorted: bool, wit: int)
  ensures sorted <==> IsSorted(a)
  ensures !sorted ==> 0 <= wit < |a| - 1 && a[wit] > a[wit + 1]

method TestSorted()
{
  var a := [1, 2, 3, 4, 5];
  var s, w := IsSortedCheck(a);
  assert s;
}

method TestUnsorted()
{
  var a := [1, 3, 2, 4];
  var s, w := IsSortedCheck(a);
  assert !IsSorted(a) by {
    assert a[1] == 3 > 2 == a[2];
  }
  assert !s;
}

method TestEmpty()
{
  var a: seq<int> := [];
  var s, w := IsSortedCheck(a);
  assert s;
}

method TestSingle()
{
  var a := [42];
  var s, w := IsSortedCheck(a);
  assert s;
}

method TestAllEqual()
{
  var a := [5, 5, 5, 5];
  var s, w := IsSortedCheck(a);
  assert s;
}

method TestDescending()
{
  var a := [5, 4, 3, 2, 1];
  var s, w := IsSortedCheck(a);
  assert !IsSorted(a) by {
    assert a[0] == 5 > 4 == a[1];
  }
  assert !s;
}
