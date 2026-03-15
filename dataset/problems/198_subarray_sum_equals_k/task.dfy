// Subarray Sum Equals K
// Task: Add loop invariants so that Dafny can verify this program.

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
