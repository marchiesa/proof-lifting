// Find All Pairs with Given Difference -- Test cases

function Abs(x: int): int { if x >= 0 then x else -x }

function PairDiffFrom(a: seq<int>, diff: int, i: int, j: int): int
  requires 0 <= i < |a| && i < j
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

method Main()
{
  // [1, 5, 3, 4, 2] with diff=2: pairs (1,3),(5,3),(3,5?no),(4,2),(1,3)...
  // Pairs: (1,3), (5,3), (4,2) => 3 pairs
  expect TotalPairDiff([1, 5, 3, 4, 2], 2, 0) == 3, "3 pairs with diff 2";
  expect TotalPairDiff([1, 2, 3], 1, 0) == 2, "2 pairs with diff 1 in [1,2,3]";
  expect TotalPairDiff([1, 1, 1], 0, 0) == 3, "3 pairs with diff 0 in [1,1,1]";
  expect TotalPairDiff([1, 2, 3], 5, 0) == 0, "0 pairs with diff 5";
  expect TotalPairDiff([], 1, 0) == 0, "Empty has 0 pairs";

  // Negative cases
  expect TotalPairDiff([1, 2, 3], 1, 0) != 3, "[1,2,3] doesn't have 3 pairs with diff 1";

  print "All spec tests passed\n";
}
