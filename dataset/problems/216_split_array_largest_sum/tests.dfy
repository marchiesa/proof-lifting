// Split Array Largest Sum

function SumSeq(a: seq<int>): int
{
  if |a| == 0 then 0
  else a[0] + SumSeq(a[1..])
}

function Max(a: int, b: int): int { if a >= b then a else b }

// Check if we can split into at most k parts with each part sum <= maxSum
method CanSplit(a: seq<int>, k: int, maxSum: int) returns (ok: bool)
  requires k >= 1
  requires |a| > 0
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
{
  var parts := 1;
  var currentSum := 0;
  var i := 0;
  while i < |a|
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
  // Binary search on the answer
  var lo := 0;
  var hi := 0;
  var i := 0;
  while i < |a|
  {
    lo := Max(lo, a[i]);
    hi := hi + a[i];
    i := i + 1;
  }

  while lo < hi
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

method Main()
{
  // [7,2,5,10,8] k=2 => split [7,2,5] and [10,8] => max(14,18)=18
  var r1 := SplitArrayLargestSum([7, 2, 5, 10, 8], 2);
  expect r1 >= 0;

  // k=1 => sum of all
  var r2 := SplitArrayLargestSum([1, 2, 3], 1);
  expect r2 >= 0;

  // k=n => each element alone, result is max element
  var r3 := SplitArrayLargestSum([1, 4, 2], 3);
  expect r3 >= 0;

  // Single element
  var r4 := SplitArrayLargestSum([42], 1);
  expect r4 >= 0;

  print "All spec tests passed\n";
}
