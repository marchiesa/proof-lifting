// Two Sum (Sorted Array) -- Test cases

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate HasPairSum(a: seq<int>, target: int)
{
  exists i, j :: 0 <= i < j < |a| && a[i] + a[j] == target
}

method {:axiom} TwoSum(a: seq<int>, target: int) returns (found: bool, lo_idx: int, hi_idx: int)
  requires IsSorted(a)
  ensures found ==> 0 <= lo_idx < hi_idx < |a| && a[lo_idx] + a[hi_idx] == target
  ensures !found ==> !HasPairSum(a, target)

method TestPairExists()
{
  var a := [1, 2, 3, 4, 6];
  var found, i, j := TwoSum(a, 8);
  assert a[1] + a[4] == 8;  // witness
  assert HasPairSum(a, 8);
  assert found;
}

method TestNoPair()
{
  var a := [1, 2, 3, 4, 6];
  var found, i, j := TwoSum(a, 20);
  assert !found;
}

method TestEmpty()
{
  var a: seq<int> := [];
  var found, i, j := TwoSum(a, 5);
  assert !found;
}

method TestSingleElement()
{
  var a := [5];
  var found, i, j := TwoSum(a, 10);
  assert !found;
}

method TestTwoElements()
{
  var a := [3, 7];
  var found, i, j := TwoSum(a, 10);
  assert a[0] + a[1] == 10;
  assert HasPairSum(a, 10);
  assert found;
}
