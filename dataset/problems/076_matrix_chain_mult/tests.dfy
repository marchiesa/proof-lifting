// Matrix Chain Multiplication -- Runtime spec tests

// The spec is `ensures true`, so we include the method and test expected outputs.

method MatrixChain(dims: seq<nat>) returns (cost: nat)
  requires |dims| >= 2
  ensures true
{
  var n := |dims| - 1;
  if n == 0 { return 0; }
  var dp := new nat[n, n];
  var i := 0;
  while i < n
  {
    dp[i, i] := 0;
    i := i + 1;
  }
  var length := 2;
  while length <= n
  {
    i := 0;
    while i <= n - length
    {
      var j := i + length - 1;
      dp[i, j] := 0xFFFF_FFFF;
      var k := i;
      while k < j
      {
        var q := dp[i, k] + dp[k + 1, j] + dims[i] * dims[k + 1] * dims[j + 1];
        if q < dp[i, j] {
          dp[i, j] := q;
        }
        k := k + 1;
      }
      i := i + 1;
    }
    length := length + 1;
  }
  cost := dp[0, n - 1];
}

method Main()
{
  // Test 1: Two matrices (10x30)(30x5) => cost = 10*30*5 = 1500
  var c := MatrixChain([10, 30, 5]);
  expect c == 1500, "Two matrices: 10x30 * 30x5 should cost 1500";

  // Test 2: Single matrix => cost = 0
  c := MatrixChain([10, 20]);
  expect c == 0, "Single matrix should cost 0";

  // Test 3: Classic example [10, 30, 5, 60]
  // Option 1: (A1*A2)*A3 = 10*30*5 + 10*5*60 = 1500 + 3000 = 4500
  // Option 2: A1*(A2*A3) = 30*5*60 + 10*30*60 = 9000 + 18000 = 27000
  // Minimum = 4500
  c := MatrixChain([10, 30, 5, 60]);
  expect c == 4500, "MatrixChain([10,30,5,60]) should be 4500";

  // Test 4: [40, 20, 30, 10, 30]
  c := MatrixChain([40, 20, 30, 10, 30]);
  expect c == 26000, "MatrixChain([40,20,30,10,30]) should be 26000";

  // Test 5: Identical dimensions [5, 5, 5, 5]
  c := MatrixChain([5, 5, 5, 5]);
  expect c == 250, "MatrixChain([5,5,5,5]) should be 250";

  // Negative: wrong values
  c := MatrixChain([10, 30, 5]);
  expect c != 1501, "Cost should not be 1501";
  expect c != 0, "Cost should not be 0 for two matrices";

  print "All spec tests passed\n";
}
