// Kth Smallest in Sorted Matrix -- Reference solution with invariants

function Min(a: int, b: int): int { if a <= b then a else b }

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
    while j < n && matrix[i * n + j] <= target
      invariant 0 <= j <= n
      decreases n - j
    {
      j := j + 1;
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
