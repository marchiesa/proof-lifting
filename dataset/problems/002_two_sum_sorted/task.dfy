// Two Sum (Sorted Array)
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate HasPairSum(a: seq<int>, target: int)
{
  exists i, j :: 0 <= i < j < |a| && a[i] + a[j] == target
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
  {
    var sum := a[lo] + a[hi];
    if sum == target {
      return true, lo, hi;
    } else if sum < target {
      lo := lo + 1;
    } else {
      hi := hi - 1;
    }
  }
  return false, 0, 0;
}
