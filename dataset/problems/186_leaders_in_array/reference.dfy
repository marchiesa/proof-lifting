// Leaders in Array -- Reference solution with invariants

predicate IsLeader(a: seq<int>, i: int)
  requires 0 <= i < |a|
{
  forall j :: i < j < |a| ==> a[i] >= a[j]
}

function MaxFrom(a: seq<int>, i: int): int
  requires 0 <= i < |a|
  decreases |a| - i
{
  if i == |a| - 1 then a[i]
  else if a[i] >= MaxFrom(a, i + 1) then a[i]
  else MaxFrom(a, i + 1)
}

method FindLeaders(a: seq<int>) returns (leaders: seq<int>)
  requires |a| > 0
  ensures forall x :: x in leaders ==> x in a
  ensures forall i :: 0 <= i < |a| && IsLeader(a, i) ==> a[i] in leaders
{
  leaders := [a[|a| - 1]];
  var maxFromRight := a[|a| - 1];
  var i := |a| - 2;
  while i >= 0
    invariant -1 <= i <= |a| - 2
    invariant forall x :: x in leaders ==> x in a
    invariant maxFromRight == MaxFrom(a, i + 1)
    invariant forall k :: i + 1 <= k < |a| && IsLeader(a, k) ==> a[k] in leaders
    decreases i + 1
  {
    if a[i] >= maxFromRight {
      maxFromRight := a[i];
      leaders := [a[i]] + leaders;
    }
    i := i - 1;
  }
}
