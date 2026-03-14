// Matrix Multiplication -- Runtime spec tests

predicate ValidMatrix(m: seq<seq<int>>, rows: int, cols: int)
{
  |m| == rows && rows >= 0 && cols >= 0 &&
  forall i | 0 <= i < rows :: |m[i]| == cols
}

function DotProduct(a: seq<int>, b: seq<seq<int>>, col: int, n: int, k: int): int
  requires 0 <= k <= n
  requires |a| >= n
  requires |b| >= n
  requires 0 <= col
  requires forall i | 0 <= i < n :: col < |b[i]|
  decreases k
{
  if k == 0 then 0
  else DotProduct(a, b, col, n, k - 1) + a[k - 1] * b[k - 1][col]
}

method Main()
{
  // Test ValidMatrix
  expect ValidMatrix([[1, 2], [3, 4]], 2, 2), "2x2 matrix valid";
  expect ValidMatrix([[1, 2, 3]], 1, 3), "1x3 matrix valid";
  expect ValidMatrix([], 0, 0), "empty matrix valid";
  expect !ValidMatrix([[1, 2], [3]], 2, 2), "ragged matrix not valid";
  expect !ValidMatrix([[1, 2]], 2, 2), "wrong row count not valid";

  // Test DotProduct
  var A := [[1, 2], [3, 4]];
  var B := [[5, 6], [7, 8]];

  // DotProduct(A[0], B, 0, 2, 2) = 1*5 + 2*7 = 19
  expect DotProduct(A[0], B, 0, 2, 2) == 19, "dot product A[0] . B[:,0] = 1*5 + 2*7 = 19";

  // DotProduct(A[0], B, 1, 2, 2) = 1*6 + 2*8 = 22
  expect DotProduct(A[0], B, 1, 2, 2) == 22, "dot product A[0] . B[:,1] = 1*6 + 2*8 = 22";

  // DotProduct(A[1], B, 0, 2, 2) = 3*5 + 4*7 = 43
  expect DotProduct(A[1], B, 0, 2, 2) == 43, "dot product A[1] . B[:,0] = 3*5 + 4*7 = 43";

  // DotProduct(A[1], B, 1, 2, 2) = 3*6 + 4*8 = 50
  expect DotProduct(A[1], B, 1, 2, 2) == 50, "dot product A[1] . B[:,1] = 3*6 + 4*8 = 50";

  // Base case
  expect DotProduct(A[0], B, 0, 2, 0) == 0, "dot product with k=0 is 0";

  // Partial dot product
  expect DotProduct(A[0], B, 0, 2, 1) == 5, "partial dot: 1*5 = 5";

  // Identity matrix test
  var I := [[1, 0], [0, 1]];
  expect DotProduct(I[0], I, 0, 2, 2) == 1, "identity: (1,0).(1,0) = 1";
  expect DotProduct(I[0], I, 1, 2, 2) == 0, "identity: (1,0).(0,1) = 0";

  print "All spec tests passed\n";
}
