// Count Range Sum
// Task: Add loop invariants so that Dafny can verify this program.
// Count subarrays whose sum falls in [lo, hi].

function SubarraySum(a: seq<int>, i: int, j: int): int
  requires 0 <= i <= j <= |a|
  decreases j - i
{
  if i == j then 0
  else a[i] + SubarraySum(a, i + 1, j)
}

function CountInRange(a: seq<int>, lo: int, hi: int, i: int, j: int): int
  requires 0 <= i <= |a|
  requires 0 <= j <= |a|
  decreases |a| - i, |a| + 1 - j
{
  if i >= |a| then 0
  else if j > |a| then CountInRange(a, lo, hi, i + 1, i + 2)
  else if j <= i then CountInRange(a, lo, hi, i, j + 1)
  else
    (if lo <= SubarraySum(a, i, j) <= hi then 1 else 0) +
    CountInRange(a, lo, hi, i, j + 1)
}

method CountRangeSum(a: seq<int>, lo: int, hi: int) returns (count: int)
  requires lo <= hi
  ensures count >= 0
{
  count := 0;
  var i := 0;
  while i < |a|
  {
    var j := i + 1;
    while j <= |a|
    {
      var s := SubarraySum(a, i, j);
      if lo <= s && s <= hi {
        count := count + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
