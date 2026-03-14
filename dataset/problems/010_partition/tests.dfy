// Partition Around Pivot -- Test cases

method {:axiom} Partition(a: seq<int>, pivot: int) returns (result: seq<int>, splitIdx: int)
  ensures |result| == |a|
  ensures 0 <= splitIdx <= |a|
  ensures forall i :: 0 <= i < splitIdx ==> result[i] <= pivot
  ensures forall i :: splitIdx <= i < |result| ==> result[i] > pivot
  ensures multiset(result) == multiset(a)

method TestMixed()
{
  var a := [3, 1, 4, 1, 5, 9];
  var r, s := Partition(a, 3);
  assert |r| == 6;
  assert 0 <= s <= 6;
}

method TestAllBelow()
{
  var a := [1, 2, 3];
  var r, s := Partition(a, 5);
  assert s == 3;
  assert |r| == 3;
}

method TestAllAbove()
{
  var a := [5, 6, 7];
  var r, s := Partition(a, 2);
  assert s == 0;
}

method TestEmpty()
{
  var a: seq<int> := [];
  var r, s := Partition(a, 5);
  assert |r| == 0;
  assert s == 0;
}

method TestSingleBelow()
{
  var a := [3];
  var r, s := Partition(a, 5);
  assert |r| == 1;
  assert s == 1;
}

method TestSingleAbove()
{
  var a := [10];
  var r, s := Partition(a, 5);
  assert |r| == 1;
  assert s == 0;
}
