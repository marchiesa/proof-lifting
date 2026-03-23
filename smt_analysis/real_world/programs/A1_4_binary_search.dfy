// Pattern: Binary search in sorted array
// Source: common utility, used in countless libraries
// Real-world: database index lookup, sorted log search, autocomplete

predicate Sorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method BinarySearch(a: seq<int>, target: int) returns (found: bool, idx: int)
  requires Sorted(a)
  ensures found ==> 0 <= idx < |a| && a[idx] == target
  ensures !found ==> forall i :: 0 <= i < |a| ==> a[i] != target
{
  var lo := 0;
  var hi := |a|;
  while lo < hi
    invariant 0 <= lo <= hi <= |a|
    invariant forall i :: 0 <= i < lo ==> a[i] < target
    invariant forall i :: hi <= i < |a| ==> a[i] > target
  {
    var mid := lo + (hi - lo) / 2;
    if a[mid] == target {
      found := true;
      idx := mid;
      return;
    } else if a[mid] < target {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  found := false;
  idx := -1;
}
