// Kth Largest Element -- Reference solution with invariants

function CountGreater(a: seq<int>, v: int): nat
{
  if |a| == 0 then 0
  else (if a[0] > v then 1 else 0) + CountGreater(a[1..], v)
}

predicate IsKthLargest(a: seq<int>, k: int, v: int)
  requires 1 <= k <= |a|
{
  v in a && CountGreater(a, v) <= k - 1 &&
  (forall x :: x in a && x > v ==> CountGreater(a, x) < k)
}

method KthLargest(a: seq<int>, k: int) returns (result: int)
  requires |a| > 0
  requires 1 <= k <= |a|
  ensures result in a
  ensures CountGreater(a, result) <= k - 1
{
  // Simple approach: sort by repeated minimum extraction
  var sorted: seq<int> := [];
  var used := seq(|a|, i => false);
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |sorted| == i
    invariant |used| == |a|
    invariant forall j :: 0 <= j < i ==> sorted[j] in a
    invariant forall j :: 0 <= j < |a| ==> used[j] ==> a[j] in sorted
    decreases |a| - i
  {
    var minVal := 0;
    var minIdx := -1;
    var j := 0;
    while j < |a|
      invariant 0 <= j <= |a|
      invariant minIdx == -1 ==> forall m :: 0 <= m < j ==> used[m]
      invariant minIdx >= 0 ==> 0 <= minIdx < |a| && !used[minIdx]
      invariant minIdx >= 0 ==> minVal == a[minIdx]
      invariant minIdx >= 0 ==> forall m :: 0 <= m < j ==> (!used[m] ==> a[m] >= minVal)
      decreases |a| - j
    {
      if !used[j] {
        if minIdx == -1 || a[j] < minVal {
          minVal := a[j];
          minIdx := j;
        }
      }
      j := j + 1;
    }
    assert minIdx >= 0;
    sorted := sorted + [a[minIdx]];
    used := used[..minIdx] + [true] + used[minIdx+1..];
    i := i + 1;
  }
  result := sorted[|a| - k];
}
