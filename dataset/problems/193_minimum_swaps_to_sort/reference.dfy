// Minimum Swaps to Sort -- Reference solution with invariants

predicate IsPermutation(a: seq<int>)
{
  (forall i :: 0 <= i < |a| ==> 0 <= a[i] < |a|) &&
  (forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j])
}

predicate IsSorted(a: seq<int>)
{
  forall i :: 0 <= i < |a| ==> a[i] == i
}

function CountFixed(a: seq<int>, n: int): nat
  requires 0 <= n <= |a|
{
  if n == 0 then 0
  else (if a[n-1] == n-1 then 1 else 0) + CountFixed(a, n-1)
}

method MinSwaps(a: seq<int>) returns (swaps: int)
  requires IsPermutation(a)
  ensures swaps >= 0
{
  var arr := a;
  swaps := 0;
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |arr| == |a|
    invariant IsPermutation(arr)
    invariant forall j :: 0 <= j < i ==> arr[j] == j
    invariant swaps >= 0
    decreases |arr| - i
  {
    if arr[i] != i {
      var target := arr[i];
      assert 0 <= target < |arr|;
      assert target != i;
      // Swap arr[i] and arr[target]
      if i < target {
        var tmp := arr[i];
        arr := arr[..i] + [arr[target]] + arr[i+1..target] + [tmp] + arr[target+1..];
      } else {
        var tmp := arr[i];
        arr := arr[..target] + [tmp] + arr[target+1..i] + [arr[target]] + arr[i+1..];
      }
      swaps := swaps + 1;
      // Don't increment i; check again
    } else {
      i := i + 1;
    }
  }
}
