// Find First Duplicate -- Reference solution with invariants

predicate HasDuplicate(a: seq<int>, idx: int)
  requires 0 <= idx < |a|
{
  exists j :: 0 <= j < idx && a[j] == a[idx]
}

predicate AllDistinctBefore(a: seq<int>, idx: int)
  requires 0 <= idx <= |a|
{
  forall i :: 0 <= i < idx ==> (forall j :: 0 <= j < i ==> a[j] != a[i])
}

method FindFirstDuplicate(a: seq<int>) returns (index: int)
  ensures index == -1 ==> AllDistinctBefore(a, |a|)
  ensures 0 <= index < |a| ==> HasDuplicate(a, index) && AllDistinctBefore(a, index)
  ensures index < 0 ==> index == -1
{
  var seen: set<int> := {};
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant seen == set k | 0 <= k < i :: a[k]
    invariant AllDistinctBefore(a, i)
    invariant forall k :: 0 <= k < i ==> a[k] in seen
    decreases |a| - i
  {
    if a[i] in seen {
      return i;
    }
    seen := seen + {a[i]};
    i := i + 1;
  }
  return -1;
}
