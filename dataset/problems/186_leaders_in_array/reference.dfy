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

lemma MaxFromBound(a: seq<int>, i: int, j: int)
  requires 0 <= i <= j < |a|
  ensures MaxFrom(a, i) >= a[j]
  decreases j - i
{
  if i == j {
    // MaxFrom(a, i) >= a[i] by definition
    if i == |a| - 1 {
    } else {
      // MaxFrom(a, i) is max(a[i], MaxFrom(a, i+1)) >= a[i]
    }
  } else {
    MaxFromBound(a, i + 1, j);
    // MaxFrom(a, i) >= MaxFrom(a, i+1) >= a[j]
  }
}

lemma MaxFromIsLeader(a: seq<int>, i: int)
  requires 0 <= i < |a|
  requires a[i] >= MaxFrom(a, i)
  ensures IsLeader(a, i)
{
  forall j | i < j < |a|
    ensures a[i] >= a[j]
  {
    MaxFromBound(a, i, j);
  }
}

lemma MaxFromNotLeader(a: seq<int>, i: int)
  requires 0 <= i < |a| - 1
  requires a[i] < MaxFrom(a, i + 1)
  ensures !IsLeader(a, i)
{
  MaxFromWitness(a, i + 1);
}

lemma MaxFromWitness(a: seq<int>, i: int)
  requires 0 <= i < |a|
  ensures exists j :: i <= j < |a| && a[j] == MaxFrom(a, i)
  decreases |a| - i
{
  if i == |a| - 1 {
    assert a[i] == MaxFrom(a, i);
    assert i <= i < |a| && a[i] == MaxFrom(a, i);
  } else if a[i] >= MaxFrom(a, i + 1) {
    assert MaxFrom(a, i) == a[i];
    assert i <= i < |a| && a[i] == MaxFrom(a, i);
  } else {
    MaxFromWitness(a, i + 1);
  }
}

lemma MaxFromUpdate(a: seq<int>, i: int)
  requires 0 <= i < |a| - 1
  ensures MaxFrom(a, i) == if a[i] >= MaxFrom(a, i + 1) then a[i] else MaxFrom(a, i + 1)
{
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
      MaxFromIsLeader(a, i);
      maxFromRight := a[i];
      leaders := [a[i]] + leaders;
    } else {
      MaxFromNotLeader(a, i);
    }
    i := i - 1;
  }
}
