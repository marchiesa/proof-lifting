// Find All Pairs with Given Difference -- Reference solution with invariants

function Abs(x: int): int
{
  if x >= 0 then x else -x
}

function PairDiffFrom(a: seq<int>, diff: int, i: int, j: int): int
  requires 0 <= i < |a|
  requires i < j
  decreases |a| - j
{
  if j >= |a| then 0
  else (if Abs(a[i] - a[j]) == diff then 1 else 0) + PairDiffFrom(a, diff, i, j + 1)
}

function TotalPairDiff(a: seq<int>, diff: int, i: int): int
  requires 0 <= i
  decreases |a| - i
{
  if i >= |a| then 0
  else if i + 1 >= |a| then 0
  else PairDiffFrom(a, diff, i, i + 1) + TotalPairDiff(a, diff, i + 1)
}

method FindPairsWithDiff(a: seq<int>, diff: int) returns (count: int)
  requires diff >= 0
  ensures count == TotalPairDiff(a, diff, 0)
{
  count := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant count + TotalPairDiff(a, diff, i) == TotalPairDiff(a, diff, 0)
    decreases |a| - i
  {
    if i + 1 >= |a| {
      i := i + 1;
    } else {
      var j := i + 1;
      while j < |a|
        invariant i + 1 <= j <= |a|
        invariant i < |a| && i + 1 < |a|
        invariant count + PairDiffFrom(a, diff, i, j) + TotalPairDiff(a, diff, i + 1) == TotalPairDiff(a, diff, 0)
        decreases |a| - j
      {
        if Abs(a[i] - a[j]) == diff {
          count := count + 1;
        }
        j := j + 1;
      }
      i := i + 1;
    }
  }
}
