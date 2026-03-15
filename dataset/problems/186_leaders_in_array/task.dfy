// Leaders in Array
// Task: Add loop invariants so that Dafny can verify this program.

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
