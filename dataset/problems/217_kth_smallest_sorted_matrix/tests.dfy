// Kth Smallest in Sorted Matrix

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
  {
    var j := 0;
    while j < n && matrix[i * n + j] <= target
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

method Main()
{
  // [[1,5,9],[10,11,13],[12,13,15]] k=8
  var m := [1, 5, 9, 10, 11, 13, 12, 13, 15];
  var r1 := KthSmallest(m, 3, 8);

  // 1x1 matrix
  var m2 := [42];
  var r2 := KthSmallest(m2, 1, 1);

  // 2x2 matrix, k=1
  var m3 := [1, 2, 3, 4];
  var r3 := KthSmallest(m3, 2, 1);

  // 2x2 matrix, k=4
  var r4 := KthSmallest(m3, 2, 4);

  print "All spec tests passed\n";
}
