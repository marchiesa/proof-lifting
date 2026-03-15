// Maximum Product Subarray -- Test cases

function Product(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 1
  else a[lo] * Product(a, lo + 1, hi)
}

method Main()
{
  // Test Product
  expect Product([2, 3, 4], 0, 3) == 24, "Product of [2,3,4] is 24";
  expect Product([2, 3, 4], 0, 0) == 1, "Empty product is 1";
  expect Product([2, 3, 4], 1, 3) == 12, "Product of [3,4] is 12";
  expect Product([-1, 2], 0, 2) == -2, "Product of [-1,2] is -2";

  // Test spec: max product of [2, 3, -2, 4]
  // Subarrays: [2]=2, [3]=3, [-2]=-2, [4]=4, [2,3]=6, [3,-2]=-6,
  // [-2,4]=-8, [2,3,-2]=-12, [3,-2,4]=-24, [2,3,-2,4]=-48
  // Max is 6
  expect Product([2, 3, -2, 4], 0, 2) == 6, "Product [2,3] is 6";
  expect Product([2, 3, -2, 4], 0, 1) == 2, "Product [2] is 2";
  expect Product([2, 3, -2, 4], 3, 4) == 4, "Product [4] is 4";
  expect Product([2, 3, -2, 4], 0, 3) == -12, "Product [2,3,-2] is -12";

  // Test that 6 is indeed the max
  expect Product([2, 3, -2, 4], 0, 2) >= Product([2, 3, -2, 4], 0, 1);
  expect Product([2, 3, -2, 4], 0, 2) >= Product([2, 3, -2, 4], 3, 4);

  print "All spec tests passed\n";
}
