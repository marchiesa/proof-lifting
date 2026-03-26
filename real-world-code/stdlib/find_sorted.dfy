// Linear search with early exit on sorted array
// (common optimization in many codebases — e.g., Redis sorted sets)
//
// If array is sorted and current element > target, we can stop early.
// Proving the early exit is correct requires instantiating the sorted
// property at specific indices.

predicate Sorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method FindSorted(a: seq<int>, target: int) returns (idx: int)
  requires Sorted(a)
  ensures idx >= 0 ==> 0 <= idx < |a| && a[idx] == target
  ensures idx < 0 ==> target !in a
{
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant target !in a[..i]
  {
    if a[i] == target { return i; }
    if a[i] > target {
      // Early exit: everything from here on is >= a[i] > target.
      return -1;
    }
    i := i + 1;
  }
  return -1;
}
