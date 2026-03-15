// Matrix Chain Multiplication -- Reference solution with invariants

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
  while i < n
    invariant 0 <= i <= n
    invariant forall a :: 0 <= a < i ==> dp[a, a] == 0
    decreases n - i
  {
    dp[i, i] := 0;
    i := i + 1;
  }

  // Initialize all off-diagonal entries to a large value
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall a :: 0 <= a < n ==> dp[a, a] == 0
    invariant forall a, b :: 0 <= a < i && 0 <= b < n && a != b ==> dp[a, b] >= 0
    decreases n - i
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant forall a :: 0 <= a < n ==> dp[a, a] == 0
      invariant forall a, b :: 0 <= a < i && 0 <= b < n && a != b ==> dp[a, b] >= 0
      invariant forall b :: 0 <= b < j && b != i ==> dp[i, b] >= 0
      decreases n - j
    {
      if j != i { dp[i, j] := 0; }
      j := j + 1;
    }
    i := i + 1;
  }

  var len := 2;
  while len <= n
    invariant 2 <= len <= n + 1
    invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> dp[a, b] >= 0
    decreases n + 1 - len
  {
    i := 0;
    while i <= n - len
      invariant 0 <= i <= n - len + 1
      invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> dp[a, b] >= 0
      decreases n - len + 1 - i
    {
      var j := i + len - 1;
      dp[i, j] := dp[i, i] + dp[i+1, j] + dims[i] * dims[i+1] * dims[j+1];
      var k := i + 1;
      while k < j
        invariant i + 1 <= k <= j
        invariant dp[i, j] >= 0
        invariant forall a, b :: 0 <= a < n && 0 <= b < n && (a != i || b != j) ==> dp[a, b] >= 0
        decreases j - k
      {
        var cost := dp[i, k] + dp[k+1, j] + dims[i] * dims[k+1] * dims[j+1];
        dp[i, j] := Min(dp[i, j], cost);
        k := k + 1;
      }
      i := i + 1;
    }
    len := len + 1;
  }

  result := dp[0, n - 1];
}
