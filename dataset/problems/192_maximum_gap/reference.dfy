// Maximum Gap -- Reference solution with invariants

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method MaxGap(a: seq<int>) returns (gap: int)
  requires |a| >= 2
  ensures gap >= 0
{
  // Sort by selection sort
  var sorted := a;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |a|
    invariant forall p, q :: 0 <= p < q < i ==> sorted[p] <= sorted[q]
    invariant forall p :: 0 <= p < i ==> forall q :: i <= q < |sorted| ==> sorted[p] <= sorted[q]
    decreases |sorted| - i
  {
    var minIdx := i;
    var j := i + 1;
    while j < |sorted|
      invariant i + 1 <= j <= |sorted|
      invariant i <= minIdx < |sorted|
      invariant forall k :: i <= k < j ==> sorted[minIdx] <= sorted[k]
      decreases |sorted| - j
    {
      if sorted[j] < sorted[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      var tmp := sorted[i];
      sorted := sorted[..i] + [sorted[minIdx]] + sorted[i+1..minIdx] + [tmp] + sorted[minIdx+1..];
    }
    i := i + 1;
  }

  // Find max gap
  gap := 0;
  i := 1;
  while i < |sorted|
    invariant 1 <= i <= |sorted|
    invariant gap >= 0
    invariant forall k :: 1 <= k < i ==> sorted[k] - sorted[k-1] <= gap
    decreases |sorted| - i
  {
    var diff := sorted[i] - sorted[i-1];
    if diff > gap {
      gap := diff;
    }
    i := i + 1;
  }
}
