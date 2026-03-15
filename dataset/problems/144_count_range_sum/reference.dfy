// Count Range Sum -- Reference solution with invariants

function SubarraySum(a: seq<int>, i: int, j: int): int
  requires 0 <= i <= j <= |a|
  decreases j - i
{
  if i == j then 0
  else a[i] + SubarraySum(a, i + 1, j)
}

method CountRangeSum(a: seq<int>, lo: int, hi: int) returns (count: int)
  requires lo <= hi
  ensures count >= 0
{
  count := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant count >= 0
    decreases |a| - i
  {
    var j := i + 1;
    while j <= |a|
      invariant i + 1 <= j <= |a| + 1
      invariant count >= 0
      decreases |a| + 1 - j
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
