// Binary Search
// Task: Add loop invariants so that Dafny can verify this program.

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
