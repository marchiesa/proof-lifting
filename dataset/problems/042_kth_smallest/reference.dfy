// Kth Smallest Element (Selection via partial sorting) -- Reference solution with invariants

method KthSmallest(a: seq<int>, k: nat) returns (result: int)
  requires |a| > 0
  requires 0 <= k < |a|
  ensures result in multiset(a)
{
  var arr := new int[|a|];
  var idx := 0;
  while idx < |a|
    invariant 0 <= idx <= |a|
    invariant forall m :: 0 <= m < idx ==> arr[m] == a[m]
    decreases |a| - idx
  {
    arr[idx] := a[idx];
    idx := idx + 1;
  }
  assert arr[..] == a;

  // Partial selection sort: sort elements 0..k
  var i := 0;
  while i <= k
    invariant 0 <= i <= k + 1
    invariant multiset(arr[..]) == multiset(a)
    invariant forall p, q :: 0 <= p < i && i <= q < arr.Length ==> arr[p] <= arr[q]
    invariant forall p, q :: 0 <= p < q < i ==> arr[p] <= arr[q]
    decreases k + 1 - i
  {
    var minIdx := i;
    var j := i + 1;
    while j < arr.Length
      invariant i + 1 <= j <= arr.Length
      invariant i <= minIdx < j
      invariant forall m :: i <= m < j ==> arr[minIdx] <= arr[m]
      decreases arr.Length - j
    {
      if arr[j] < arr[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    arr[minIdx], arr[i] := arr[i], arr[minIdx];
    i := i + 1;
  }
  result := arr[k];
  assert result in multiset(arr[..]);
}
