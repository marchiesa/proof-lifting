// Interval Scheduling (Greedy) -- Test cases

predicate SortedByEnd(ends: seq<int>)
{
  forall i, j :: 0 <= i < j < |ends| ==> ends[i] <= ends[j]
}

method {:axiom} IntervalSchedule(starts: seq<int>, ends: seq<int>) returns (count: int, selected: seq<int>)
  requires |starts| == |ends|
  requires SortedByEnd(ends)
  requires forall i :: 0 <= i < |starts| ==> starts[i] < ends[i]
  ensures 0 <= count <= |starts|
  ensures |selected| == count
  ensures forall i :: 0 <= i < count ==> 0 <= selected[i] < |starts|
  ensures forall i, j :: 0 <= i < j < count ==> selected[i] < selected[j]
  ensures forall i, j :: 0 <= i < j < count ==>
    ends[selected[i]] <= starts[selected[j]]

method TestBasic()
{
  var starts := [1, 3, 0, 5, 8, 5];
  var ends := [2, 4, 6, 7, 9, 9];
  var count, sel := IntervalSchedule(starts, ends);
  assert 0 <= count <= 6;
}

method TestAllOverlapping()
{
  var starts := [1, 2, 3];
  var ends := [10, 11, 12];
  var count, sel := IntervalSchedule(starts, ends);
  assert 0 <= count <= 3;
}

method TestEmpty()
{
  var starts: seq<int> := [];
  var ends: seq<int> := [];
  var count, sel := IntervalSchedule(starts, ends);
  assert count == 0;
}

method TestSingle()
{
  var starts := [1];
  var ends := [5];
  var count, sel := IntervalSchedule(starts, ends);
  assert 0 <= count <= 1;
}
