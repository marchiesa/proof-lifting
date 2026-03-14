// Count Inversions -- Runtime spec tests

// Copy spec functions from task.dfy
function InvCount(a: seq<int>, i: int, j: int): int
  requires 0 <= i <= |a|
  requires 0 <= j <= |a|
  decreases |a| - j
{
  if i >= |a| || j >= |a| then 0
  else if i >= j then 0
  else (if a[i] > a[j] then 1 else 0) + InvCount(a, i, j + 1)
}

function TotalInvFrom(a: seq<int>, i: int): int
  requires 0 <= i <= |a|
  decreases |a| - i
{
  if i >= |a| then 0
  else InvCount(a, i, i + 1) + TotalInvFrom(a, i + 1)
}

function TotalInversions(a: seq<int>): int
{
  TotalInvFrom(a, 0)
}

method Main()
{
  // Test 1: sorted array has 0 inversions
  expect TotalInversions([1, 2, 3]) == 0, "[1,2,3] should have 0 inversions";

  // Test 2: reverse sorted has max inversions
  expect TotalInversions([3, 2, 1]) == 3, "[3,2,1] should have 3 inversions";

  // Test 3: single inversion
  expect TotalInversions([2, 1]) == 1, "[2,1] should have 1 inversion";

  // Test 4: empty array
  expect TotalInversions([]) == 0, "[] should have 0 inversions";

  // Test 5: single element
  expect TotalInversions([5]) == 0, "[5] should have 0 inversions";

  // Test 6: [3,1,2] has 2 inversions: (3,1) and (3,2)
  expect TotalInversions([3, 1, 2]) == 2, "[3,1,2] should have 2 inversions";

  // Test 7: [4,3,2,1] has 6 inversions
  expect TotalInversions([4, 3, 2, 1]) == 6, "[4,3,2,1] should have 6 inversions";

  // Negative tests
  expect TotalInversions([1, 2, 3]) != 1, "[1,2,3] should not have 1 inversion";
  expect TotalInversions([3, 2, 1]) != 2, "[3,2,1] should not have 2 inversions";

  // Test InvCount helper directly
  expect InvCount([3, 1, 2], 0, 1) == 2, "InvCount([3,1,2], 0, 1) should be 2";
  expect InvCount([1, 2, 3], 0, 1) == 0, "InvCount([1,2,3], 0, 1) should be 0";

  print "All spec tests passed\n";
}
