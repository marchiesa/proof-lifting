// Shortest Unsorted Continuous Subarray -- Reference solution with invariants

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

method ShortestUnsorted(a: seq<int>) returns (length: int)
  ensures length >= 0
  ensures length <= |a|
  ensures length == 0 ==> IsSorted(a)
{
  if |a| <= 1 {
    return 0;
  }
  var left := 0;
  while left < |a| - 1 && a[left] <= a[left + 1]
    invariant 0 <= left <= |a| - 1
    invariant forall p, q :: 0 <= p < q <= left ==> a[p] <= a[q]
    decreases |a| - 1 - left
  {
    left := left + 1;
  }
  if left == |a| - 1 {
    assert forall p, q :: 0 <= p < q < |a| ==> a[p] <= a[q];
    return 0;
  }
  var right := |a| - 1;
  while right > 0 && a[right] >= a[right - 1]
    invariant 0 <= right <= |a| - 1
    invariant forall p, q :: right <= p < q < |a| ==> a[p] <= a[q]
    decreases right
  {
    right := right - 1;
  }
  var minVal := a[left];
  var maxVal := a[left];
  var i := left;
  while i <= right
    invariant left <= i <= right + 1
    invariant forall k :: left <= k < i ==> minVal <= a[k] && a[k] <= maxVal
    decreases right + 1 - i
  {
    minVal := Min(minVal, a[i]);
    maxVal := Max(maxVal, a[i]);
    i := i + 1;
  }
  while left > 0 && a[left - 1] > minVal
    invariant 0 <= left
    decreases left
  {
    left := left - 1;
  }
  while right < |a| - 1 && a[right + 1] < maxVal
    invariant right < |a|
    decreases |a| - 1 - right
  {
    right := right + 1;
  }
  length := right - left + 1;
}
