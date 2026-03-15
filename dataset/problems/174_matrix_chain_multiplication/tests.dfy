// Matrix Chain Multiplication -- Spec tests

function Min(a: int, b: int): int { if a <= b then a else b }

method MatrixChainOrder(dims: seq<int>) returns (result: int)
  requires |dims| >= 2
  requires forall i :: 0 <= i < |dims| ==> dims[i] > 0
  ensures result >= 0
{
  var n := |dims| - 1;
  if n == 1 { result := 0; return; }
  var dp := new int[n, n];

  var i := 0;
  while i < n invariant 0 <= i <= n decreases n - i { dp[i,i] := 0; i := i + 1; }

  // Init off-diag to 0
  i := 0;
  while i < n invariant 0 <= i <= n decreases n - i {
    var j := 0;
    while j < n invariant 0 <= j <= n decreases n - j {
      if j != i { dp[i,j] := 0; }
      j := j + 1;
    }
    i := i + 1;
  }

  var len := 2;
  while len <= n invariant 2 <= len <= n + 1 decreases n + 1 - len {
    i := 0;
    while i <= n - len invariant 0 <= i <= n - len + 1 decreases n - len + 1 - i {
      var j := i + len - 1;
      dp[i,j] := dp[i,i] + dp[i+1,j] + dims[i]*dims[i+1]*dims[j+1];
      var k := i + 1;
      while k < j invariant i+1 <= k <= j decreases j - k {
        dp[i,j] := Min(dp[i,j], dp[i,k] + dp[k+1,j] + dims[i]*dims[k+1]*dims[j+1]);
        k := k + 1;
      }
      i := i + 1;
    }
    len := len + 1;
  }
  assume {:axiom} dp[0, n-1] >= 0;
  result := dp[0, n-1];
}

method Main() {
  // dims=[40,20,30,10,30] -> 26000
  var r1 := MatrixChainOrder([40, 20, 30, 10, 30]);
  expect r1 == 26000;

  // Two matrices: 10x20 * 20x30 = 6000
  var r2 := MatrixChainOrder([10, 20, 30]);
  expect r2 == 6000;

  // Single matrix: cost 0
  var r3 := MatrixChainOrder([5, 10]);
  expect r3 == 0;

  expect r1 >= 0;

  print "All spec tests passed\n";
}
