// Counting Sort -- Test cases

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method {:axiom} CountingSort(a: seq<int>, maxVal: int) returns (result: seq<int>)
  requires maxVal > 0
  requires forall i :: 0 <= i < |a| ==> 0 <= a[i] < maxVal
  ensures IsSorted(result)
  ensures |result| == |a|
  ensures multiset(result) == multiset(a)

method TestBasic()
{
  var a := [3, 1, 4, 1, 5];
  var r := CountingSort(a, 6);
  assert IsSorted(r);
  assert |r| == 5;
  assert multiset(r) == multiset(a);
  assert 1 in multiset(r);
  assert 5 in multiset(r);
}

method TestEmpty()
{
  var a: seq<int> := [];
  var r := CountingSort(a, 10);
  assert |r| == 0;
}

method TestAllSame()
{
  var a := [0, 0, 0];
  var r := CountingSort(a, 1);
  assert |r| == 3;
  assert IsSorted(r);
}

method TestAlreadySorted()
{
  var a := [1, 2, 3, 4];
  var r := CountingSort(a, 5);
  assert |r| == 4;
  assert multiset(r) == multiset(a);
}
