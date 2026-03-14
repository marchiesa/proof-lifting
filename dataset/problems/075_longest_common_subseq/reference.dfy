// Longest Common Subsequence (DP) -- Reference solution with invariants

function LCSLen(a: seq<int>, b: seq<int>): nat
  decreases |a|, |b|
{
  if |a| == 0 || |b| == 0 then 0
  else if a[|a|-1] == b[|b|-1] then 1 + LCSLen(a[..|a|-1], b[..|b|-1])
  else Max(LCSLen(a[..|a|-1], b), LCSLen(a, b[..|b|-1]))
}

function Max(x: int, y: int): int { if x >= y then x else y }

method ComputeLCS(a: seq<int>, b: seq<int>) returns (result: nat)
  ensures result == LCSLen(a, b)
{
  var m := |a|;
  var n := |b|;
  var dp := new int[m + 1, n + 1];

  // Initialize row 0 and column 0
  var i := 0;
  while i <= m
    invariant 0 <= i <= m + 1
    invariant forall ii :: 0 <= ii < i ==> dp[ii, 0] == 0
    decreases m + 1 - i
  {
    dp[i, 0] := 0;
    i := i + 1;
  }
  var j := 0;
  while j <= n
    invariant 0 <= j <= n + 1
    invariant forall ii :: 0 <= ii <= m ==> dp[ii, 0] == 0
    invariant forall jj :: 0 <= jj < j ==> dp[0, jj] == 0
    decreases n + 1 - j
  {
    dp[0, j] := 0;
    j := j + 1;
  }

  // Fill DP table row by row
  i := 1;
  while i <= m
    invariant 1 <= i <= m + 1
    invariant forall ii :: 0 <= ii <= m ==> dp[ii, 0] == 0
    invariant forall jj :: 0 <= jj <= n ==> dp[0, jj] == 0
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> dp[ii, jj] == LCSLen(a[..ii], b[..jj])
    decreases m + 1 - i
  {
    j := 1;
    while j <= n
      invariant 1 <= j <= n + 1
      invariant forall ii :: 0 <= ii <= m ==> dp[ii, 0] == 0
      invariant forall jj :: 0 <= jj <= n ==> dp[0, jj] == 0
      invariant forall jj :: 1 <= jj < j ==> dp[i, jj] == LCSLen(a[..i], b[..jj])
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> dp[ii, jj] == LCSLen(a[..ii], b[..jj])
      decreases n + 1 - j
    {
      assert a[..i][..|a[..i]|-1] == a[..i-1];
      assert b[..j][..|b[..j]|-1] == b[..j-1];
      if a[i-1] == b[j-1] {
        dp[i, j] := dp[i-1, j-1] + 1;
      } else {
        dp[i, j] := Max(dp[i-1, j], dp[i, j-1]);
      }
      j := j + 1;
    }
    // After filling row i, prove dp[i, 0] == LCSLen(a[..i], b[..0])
    assert dp[i, 0] == 0;
    assert b[..0] == [];
    assert LCSLen(a[..i], []) == 0;
    i := i + 1;
  }
  assert a[..m] == a;
  assert b[..n] == b;
  result := dp[m, n];
}
