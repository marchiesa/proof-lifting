// Linear Search -- Reference solution with invariants

method LinearSearch(a: seq<int>, threshold: int) returns (index: int)
  ensures index == -1 ==> forall k :: 0 <= k < |a| ==> a[k] <= threshold
  ensures 0 <= index < |a| ==> a[index] > threshold
  ensures 0 <= index < |a| ==> forall j :: 0 <= j < index ==> a[j] <= threshold
  ensures index < 0 ==> index == -1
{
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < i ==> a[j] <= threshold
    decreases |a| - i
  {
    if a[i] > threshold {
      return i;
    }
    i := i + 1;
  }
  return -1;
}
