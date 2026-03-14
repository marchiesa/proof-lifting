// Matrix Multiplication -- Test cases

function DotProduct(a: seq<int>, b: seq<seq<int>>, col: int, n: int, k: int): int
  requires 0 <= k <= n
  requires |a| >= n
  requires |b| >= n
  requires 0 <= col
  requires forall i :: 0 <= i < n ==> col < |b[i]|
  decreases k
{
  if k == 0 then 0
  else DotProduct(a, b, col, n, k - 1) + a[k - 1] * b[k - 1][col]
}

method {:axiom} MatMul(A: seq<seq<int>>, B: seq<seq<int>>) returns (C: seq<seq<int>>)
  requires |A| > 0 && |B| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |B|
  requires forall j :: 0 <= j < |B| ==> |B[j]| == |B[0]|
  requires |B[0]| > 0
  ensures |C| == |A|
  ensures forall i :: 0 <= i < |C| ==> |C[i]| == |B[0]|
  ensures forall i, j :: 0 <= i < |C| && 0 <= j < |C[i]|
            ==> C[i][j] == DotProduct(A[i], B, j, |B|, |B|)

method TestBasic()
{
  var A := [[1, 2], [3, 4]];
  var B := [[5, 6], [7, 8]];
  var C := MatMul(A, B);
  assert |C| == 2;
  assert |C[0]| == 2;
  assert |C[1]| == 2;
}

method TestDimensions()
{
  var A := [[1, 0], [0, 1], [1, 1]];
  var B := [[5, 6, 7], [8, 9, 10]];
  var C := MatMul(A, B);
  assert |C| == 3;
  assert |C[0]| == 3;
}

method TestSingleElement()
{
  var A := [[3]];
  var B := [[4]];
  var C := MatMul(A, B);
  assert |C| == 1;
  assert |C[0]| == 1;
}
