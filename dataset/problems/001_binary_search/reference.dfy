// Binary Search -- Reference solution with invariants

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method BinarySearch(a: seq<int>, target: int) returns (index: int)
  requires IsSorted(a)
  ensures index == -1 ==> forall k :: 0 <= k < |a| ==> a[k] != target
  ensures 0 <= index < |a| ==> a[index] == target
  ensures index < 0 ==> index == -1
{
  var lo := 0;
  var hi := |a|;
  while lo < hi
    invariant 0 <= lo <= hi <= |a|
    invariant forall k :: 0 <= k < lo ==> a[k] != target
    invariant forall k :: hi <= k < |a| ==> a[k] != target
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    if a[mid] == target {
      return mid;
    } else if a[mid] < target {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  return -1;
}
