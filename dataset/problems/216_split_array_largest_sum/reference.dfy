// Split Array Largest Sum -- Reference solution with invariants

function Max(a: int, b: int): int { if a >= b then a else b }

method CanSplit(a: seq<int>, k: int, maxSum: int) returns (ok: bool)
  requires k >= 1
  requires |a| > 0
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
{
  var parts := 1;
  var currentSum := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant parts >= 1
    invariant currentSum >= 0
    decreases |a| - i
  {
    if a[i] > maxSum {
      ok := false;
      return;
    }
    if currentSum + a[i] > maxSum {
      parts := parts + 1;
      currentSum := a[i];
    } else {
      currentSum := currentSum + a[i];
    }
    i := i + 1;
  }
  ok := parts <= k;
}

method SplitArrayLargestSum(a: seq<int>, k: int) returns (result: int)
  requires |a| > 0
  requires 1 <= k <= |a|
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures result >= 0
{
  var lo := 0;
  var hi := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant lo >= 0
    invariant hi >= 0
    invariant lo <= hi
    decreases |a| - i
  {
    lo := Max(lo, a[i]);
    hi := hi + a[i];
    i := i + 1;
  }

  while lo < hi
    invariant 0 <= lo <= hi
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    var ok := CanSplit(a, k, mid);
    if ok {
      hi := mid;
    } else {
      lo := mid + 1;
    }
  }
  result := lo;
}
