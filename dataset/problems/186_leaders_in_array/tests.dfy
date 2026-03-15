// Leaders in Array

predicate IsLeader(a: seq<int>, i: int)
  requires 0 <= i < |a|
{
  forall j :: i < j < |a| ==> a[i] >= a[j]
}

method FindLeaders(a: seq<int>) returns (leaders: seq<int>)
  requires |a| > 0
  ensures forall x :: x in leaders ==> x in a
  ensures forall i :: 0 <= i < |a| && IsLeader(a, i) ==> a[i] in leaders
{
  leaders := [];
  var maxFromRight := a[|a| - 1];
  leaders := [a[|a| - 1]];
  var i := |a| - 2;
  while i >= 0
  {
    if a[i] >= maxFromRight {
      maxFromRight := a[i];
      leaders := [a[i]] + leaders;
    }
    i := i - 1;
  }
}

method Main()
{
  // [16, 17, 4, 3, 5, 2] => leaders are 17, 5, 2
  var a := [16, 17, 4, 3, 5, 2];
  var r := FindLeaders(a);
  // Last element is always a leader
  expect IsLeader(a, 5);
  expect 2 in r;
  // 17 is a leader (>= all to its right)
  expect IsLeader(a, 1);
  expect 17 in r;
  // 5 >= 2 so it's a leader
  expect IsLeader(a, 4);
  expect 5 in r;
  // 4 is not a leader (4 < 5)
  expect !IsLeader(a, 2);

  // All same => all are leaders
  var b := [3, 3, 3];
  var rb := FindLeaders(b);
  expect IsLeader(b, 0);
  expect IsLeader(b, 1);
  expect IsLeader(b, 2);
  expect 3 in rb;

  // Single element
  var c := [42];
  var rc := FindLeaders(c);
  expect 42 in rc;

  print "All spec tests passed\n";
}
