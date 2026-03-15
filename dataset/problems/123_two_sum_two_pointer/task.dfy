// Two Sum (Two Pointer)
// Task: Add loop invariants so that Dafny can verify this program.
// Check if a sorted array has two elements summing to a target.

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
  {
    var s := a[lo] + a[hi];
    if s == target {
      return true, lo, hi;
    } else if s < target {
      lo := lo + 1;
    } else {
      hi := hi - 1;
    }
  }
  return false, 0, 0;
}
