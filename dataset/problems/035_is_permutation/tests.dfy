// Check if Array is a Permutation of 0..n-1 -- Test cases

predicate IsPermutation(a: seq<int>)
{
  (forall i :: 0 <= i < |a| ==> 0 <= a[i] < |a|) &&
  (forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j])
}

method {:axiom} CheckPermutation(a: seq<int>) returns (result: bool)
  ensures result == IsPermutation(a)

method TestValid()
{
  var r := CheckPermutation([2, 0, 1]);
  assert IsPermutation([2, 0, 1]);
  assert r;
}

method TestInvalidRange()
{
  var r := CheckPermutation([0, 1, 5]);
  assert !IsPermutation([0, 1, 5]) by {
    assert [0, 1, 5][2] == 5;
    assert !(0 <= 5 < 3);
  }
  assert !r;
}

method TestDuplicate()
{
  var r := CheckPermutation([0, 1, 1]);
  assert !IsPermutation([0, 1, 1]) by {
    assert [0, 1, 1][1] == [0, 1, 1][2];
  }
  assert !r;
}

method TestEmpty()
{
  var r := CheckPermutation([]);
  assert IsPermutation([]);
  assert r;
}

method TestSingleton()
{
  var r := CheckPermutation([0]);
  assert IsPermutation([0]);
  assert r;
}
