// Kth Largest Element
// Task: Add loop invariants so that Dafny can verify this program.

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
  // Simple selection sort approach: sort then pick
  var sorted: seq<int> := [];
  var remaining := a;
  var n := |a|;
  var i := 0;
  while i < n
  {
    // Find minimum in remaining
    var minVal := remaining[0];
    var minIdx := 0;
    var j := 1;
    while j < |remaining|
    {
      if remaining[j] < minVal {
        minVal := remaining[j];
        minIdx := j;
      }
      j := j + 1;
    }
    sorted := sorted + [minVal];
    remaining := remaining[..minIdx] + remaining[minIdx+1..];
    i := i + 1;
  }
  result := sorted[n - k];
}
