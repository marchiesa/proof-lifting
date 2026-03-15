// Counting Inversions -- Test cases

function InvFrom(a: seq<int>, i: int, j: int): int
  requires 0 <= i < |a|
  requires i < j
  decreases |a| - j
{
  if j >= |a| then 0
  else (if a[i] > a[j] then 1 else 0) + InvFrom(a, i, j + 1)
}

function TotalInv(a: seq<int>, i: int): int
  requires 0 <= i
  decreases |a| - i
{
  if i >= |a| then 0
  else if i + 1 >= |a| then 0
  else InvFrom(a, i, i + 1) + TotalInv(a, i + 1)
}

method Main()
{
  // Test TotalInv
  expect TotalInv([], 0) == 0, "Empty has 0 inversions";
  expect TotalInv([1], 0) == 0, "Single has 0 inversions";
  expect TotalInv([1, 2], 0) == 0, "Sorted pair has 0 inversions";
  expect TotalInv([2, 1], 0) == 1, "Reversed pair has 1 inversion";
  expect TotalInv([3, 1, 2], 0) == 2, "[3,1,2] has 2 inversions (3>1, 3>2)";
  expect TotalInv([1, 2, 3], 0) == 0, "Sorted has 0 inversions";
  expect TotalInv([3, 2, 1], 0) == 3, "Reverse sorted has 3 inversions";

  // Test negative: wrong counts
  expect TotalInv([2, 1], 0) != 0, "[2,1] doesn't have 0 inversions";
  expect TotalInv([1, 2, 3], 0) != 1, "[1,2,3] doesn't have 1 inversion";

  print "All spec tests passed\n";
}
