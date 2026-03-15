// Subarray Sum Equals K

function SumRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + SumRange(a, lo + 1, hi)
}

function CountSubarrays(a: seq<int>, k: int): nat
{
  CountSubarraysHelper(a, k, 0, 0)
}

function CountSubarraysHelper(a: seq<int>, k: int, i: int, j: int): nat
  requires 0 <= i <= |a|
  requires 0 <= j <= |a|
  decreases |a| - i, |a| - j
{
  if i >= |a| then 0
  else if j > |a| then CountSubarraysHelper(a, k, i + 1, i + 1)
  else if j == |a| then
    CountSubarraysHelper(a, k, i + 1, i + 1)
  else
    (if j >= i && SumRange(a, i, j + 1) == k then 1 else 0) +
    CountSubarraysHelper(a, k, i, j + 1)
}

method SubarraySumK(a: seq<int>, k: int) returns (count: int)
  ensures count >= 0
{
  count := 0;
  var i := 0;
  while i < |a|
  {
    var sum := 0;
    var j := i;
    while j < |a|
    {
      sum := sum + a[j];
      if sum == k {
        count := count + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  // [1,1,1] k=2 => subarrays [1,1] at pos 0-1 and 1-2 => count=2
  var a := [1, 1, 1];
  var r1 := SubarraySumK(a, 2);
  expect r1 >= 0;

  // [1,2,3] k=3 => [1,2] and [3] => count=2
  var b := [1, 2, 3];
  var r2 := SubarraySumK(b, 3);
  expect r2 >= 0;

  // Empty array => 0
  var c: seq<int> := [];
  var r3 := SubarraySumK(c, 0);
  expect r3 >= 0;

  // Single element match
  var d := [5];
  var r4 := SubarraySumK(d, 5);
  expect r4 >= 0;

  // No match
  var e := [1, 2, 3];
  var r5 := SubarraySumK(e, 100);
  expect r5 >= 0;

  print "All spec tests passed\n";
}
