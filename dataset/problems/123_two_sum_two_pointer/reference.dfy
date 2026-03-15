// Two Sum (Two Pointer) -- Reference solution with invariants

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate HasPairSum(a: seq<int>, target: int)
{
  exists i, j :: 0 <= i < j < |a| && a[i] + a[j] == target
}

method TwoSumSorted(a: seq<int>, target: int) returns (found: bool, lo: int, hi: int)
  requires IsSorted(a)
  ensures found ==> 0 <= lo < hi < |a| && a[lo] + a[hi] == target
  ensures !found ==> !HasPairSum(a, target)
{
  if |a| < 2 {
    return false, 0, 0;
  }
  lo := 0;
  hi := |a| - 1;
  while lo < hi
    invariant 0 <= lo <= hi < |a|
    invariant forall i, j :: 0 <= i < lo && i < j < |a| ==> a[i] + a[j] != target
    invariant forall i, j :: 0 <= i < j && hi < j < |a| ==> a[i] + a[j] != target
    decreases hi - lo
  {
    var s := a[lo] + a[hi];
    if s == target {
      return true, lo, hi;
    } else if s < target {
      assert forall j :: lo < j <= hi ==> a[lo] + a[j] <= a[lo] + a[hi] < target;
      lo := lo + 1;
    } else {
      assert forall i :: lo <= i < hi ==> a[i] + a[hi] >= a[lo] + a[hi] > target;
      hi := hi - 1;
    }
  }
  assert !HasPairSum(a, target);
  return false, 0, 0;
}
