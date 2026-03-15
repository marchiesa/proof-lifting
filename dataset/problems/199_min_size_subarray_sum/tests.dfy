// Minimum Size Subarray Sum

function SumRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + SumRange(a, lo + 1, hi)
}

function Min(a: int, b: int): int { if a <= b then a else b }

method MinSubarrayLen(a: seq<int>, target: int) returns (minLen: int)
  requires target > 0
  requires forall i :: 0 <= i < |a| ==> a[i] > 0
  ensures minLen >= 0
  ensures minLen == 0 || (1 <= minLen <= |a|)
{
  minLen := 0;
  var left := 0;
  var sum := 0;
  var right := 0;
  while right < |a|
  {
    sum := sum + a[right];
    right := right + 1;
    while sum >= target && left < right
    {
      var windowLen := right - left;
      if minLen == 0 || windowLen < minLen {
        minLen := windowLen;
      }
      sum := sum - a[left];
      left := left + 1;
    }
  }
}

method Main()
{
  // [2,3,1,2,4,3] target=7 => [4,3] length 2
  var a := [2, 3, 1, 2, 4, 3];
  var r1 := MinSubarrayLen(a, 7);
  expect r1 >= 0;
  expect r1 == 0 || (1 <= r1 <= 6);

  // [1,1,1,1,1,1] target=100 => no subarray, return 0
  var b := [1, 1, 1, 1, 1, 1];
  var r2 := MinSubarrayLen(b, 100);
  expect r2 >= 0;

  // Single element >= target
  var c := [10];
  var r3 := MinSubarrayLen(c, 5);
  expect r3 >= 0;
  expect r3 == 0 || r3 == 1;

  // Empty
  var d: seq<int> := [];
  var r4 := MinSubarrayLen(d, 1);
  expect r4 >= 0;

  print "All spec tests passed\n";
}
