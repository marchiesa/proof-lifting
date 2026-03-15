// Count Range Sum -- Test cases

function SubarraySum(a: seq<int>, i: int, j: int): int
  requires 0 <= i <= j <= |a|
  decreases j - i
{
  if i == j then 0
  else a[i] + SubarraySum(a, i + 1, j)
}

method Main()
{
  expect SubarraySum([1, 2, 3], 0, 3) == 6, "Sum [1,2,3] = 6";
  expect SubarraySum([1, 2, 3], 0, 1) == 1, "Sum [1] = 1";
  expect SubarraySum([1, 2, 3], 1, 3) == 5, "Sum [2,3] = 5";
  expect SubarraySum([-1, 2], 0, 2) == 1, "Sum [-1,2] = 1";

  // Test range: in [-1, 2, 1], subarrays with sum in [0, 3]:
  // [-1]==-1 NO, [2]==2 YES, [1]==1 YES, [-1,2]==1 YES, [2,1]==3 YES, [-1,2,1]==2 YES
  // Count = 5
  expect SubarraySum([-1, 2, 1], 0, 1) == -1, "[-1]=-1";
  expect SubarraySum([-1, 2, 1], 1, 2) == 2, "[2]=2";
  expect SubarraySum([-1, 2, 1], 2, 3) == 1, "[1]=1";

  print "All spec tests passed\n";
}
