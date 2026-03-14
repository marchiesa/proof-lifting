// Matrix Multiplication -- Reference solution with invariants

predicate ValidMatrix(m: seq<seq<int>>, rows: int, cols: int)
{
  |m| == rows && rows >= 0 && cols >= 0 &&
  forall i :: 0 <= i < rows ==> |m[i]| == cols
}

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

method MatMul(A: seq<seq<int>>, B: seq<seq<int>>) returns (C: seq<seq<int>>)
  requires |A| > 0 && |B| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |B|
  requires forall j :: 0 <= j < |B| ==> |B[j]| == |B[0]|
  requires |B[0]| > 0
  ensures |C| == |A|
  ensures forall i :: 0 <= i < |C| ==> |C[i]| == |B[0]|
  ensures forall i, j :: 0 <= i < |C| && 0 <= j < |C[i]|
            ==> C[i][j] == DotProduct(A[i], B, j, |B|, |B|)
{
  var m := |A|;
  var n := |B|;
  var p := |B[0]|;
  C := [];

  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |C| == i
    invariant forall r :: 0 <= r < i ==> |C[r]| == p
    invariant forall r, c :: 0 <= r < i && 0 <= c < p
                ==> C[r][c] == DotProduct(A[r], B, c, n, n)
    decreases m - i
  {
    var row: seq<int> := [];
    var j := 0;
    while j < p
      invariant 0 <= j <= p
      invariant |row| == j
      invariant forall c :: 0 <= c < j
                  ==> row[c] == DotProduct(A[i], B, c, n, n)
      decreases p - j
    {
      var sum := 0;
      var k := 0;
      while k < n
        invariant 0 <= k <= n
        invariant sum == DotProduct(A[i], B, j, n, k)
        decreases n - k
      {
        sum := sum + A[i][k] * B[k][j];
        k := k + 1;
      }
      row := row + [sum];
      j := j + 1;
    }
    C := C + [row];
    i := i + 1;
  }
}
