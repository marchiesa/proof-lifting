// Dot Product -- Test cases

function DotProd(a: seq<int>, b: seq<int>): int
  requires |a| == |b|
  decreases |a|
{
  if |a| == 0 then 0
  else a[0] * b[0] + DotProd(a[1..], b[1..])
}

method Main()
{
  // Test DotProd - basic cases
  expect DotProd([], []) == 0, "Empty dot product is 0";
  expect DotProd([1], [1]) == 1, "[1].[1] = 1";
  expect DotProd([1, 2, 3], [4, 5, 6]) == 32, "[1,2,3].[4,5,6] = 4+10+18 = 32";
  expect DotProd([1, 0, -1], [1, 0, -1]) == 2, "[1,0,-1].[1,0,-1] = 1+0+1 = 2";

  // Test DotProd - negative
  expect DotProd([1, 2], [3, 4]) != 0, "[1,2].[3,4] != 0";
  expect DotProd([1, 2], [3, 4]) == 11, "[1,2].[3,4] = 3+8 = 11";
  expect DotProd([1, 0], [0, 1]) == 0, "Orthogonal vectors";

  // Test with negative numbers
  expect DotProd([-1, -2], [-3, -4]) == 11, "[-1,-2].[-3,-4] = 3+8 = 11";
  expect DotProd([1, -1], [-1, 1]) == -2, "[1,-1].[-1,1] = -1-1 = -2";

  print "All spec tests passed\n";
}
