// Kth Smallest in Sorted Matrix -- Reference solution with invariants

function Min(a: int, b: int): int { if a <= b then a else b }

lemma MulLemma(a: int, b: int, c: int)
  requires 0 <= a < c
  requires 0 <= b < c
  ensures a * c + b < c * c
{
  assert a <= c - 1;
  assert a * c <= (c - 1) * c;
  assert (c - 1) * c + b < c * c;
}

method CountLessEqual(matrix: seq<int>, n: int, target: int) returns (count: int)
  requires n > 0
  requires |matrix| == n * n
  ensures count >= 0
  ensures count <= n * n
{
  count := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= count <= i * n
    decreases n - i
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      decreases n - j
    {
      MulLemma(i, j, n);
      if matrix[i * n + j] <= target {
        j := j + 1;
      } else {
        break;
      }
    }
    count := count + j;
    i := i + 1;
  }
}

method KthSmallest(matrix: seq<int>, n: int, k: int) returns (result: int)
  requires n > 0
  requires |matrix| == n * n
  requires 1 <= k <= n * n
  ensures true
{
  var lo := matrix[0];
  var hi := matrix[n * n - 1];
  if lo > hi {
    result := lo;
    return;
  }
  while lo < hi
    invariant lo <= hi
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    var cnt := CountLessEqual(matrix, n, mid);
    if cnt < k {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  result := lo;
}
