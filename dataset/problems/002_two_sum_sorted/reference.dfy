// Two Sum (Sorted Array) -- Reference solution with invariants

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate HasPairSum(a: seq<int>, target: int)
{
  exists i, j :: 0 <= i < j < |a| && a[i] + a[j] == target
}

// The key invariant: any valid pair must have both indices in [lo..hi]
predicate NoPairOutside(a: seq<int>, target: int, lo: int, hi: int)
  requires 0 <= lo && hi < |a|
{
  forall i, j :: 0 <= i < j < |a| && a[i] + a[j] == target ==> lo <= i && j <= hi
}

method TwoSum(a: seq<int>, target: int) returns (found: bool, lo_idx: int, hi_idx: int)
  requires IsSorted(a)
  ensures found ==> 0 <= lo_idx < hi_idx < |a| && a[lo_idx] + a[hi_idx] == target
  ensures !found ==> !HasPairSum(a, target)
{
  if |a| < 2 {
    return false, 0, 0;
  }
  var lo := 0;
  var hi := |a| - 1;
  while lo < hi
    invariant 0 <= lo <= hi < |a|
    invariant NoPairOutside(a, target, lo, hi)
    decreases hi - lo
  {
    var sum := a[lo] + a[hi];
    if sum == target {
      return true, lo, hi;
    } else if sum < target {
      assert forall j :: lo < j <= hi ==> a[lo] + a[j] <= a[lo] + a[hi] < target;
      lo := lo + 1;
    } else {
      assert forall i :: lo <= i < hi ==> a[i] + a[hi] >= a[lo] + a[hi] > target;
      hi := hi - 1;
    }
  }
  return false, 0, 0;
}
