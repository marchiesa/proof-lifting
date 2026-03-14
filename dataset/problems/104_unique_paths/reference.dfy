// Unique Paths in Grid (DP) -- Reference solution with invariants

function Paths(m: nat, n: nat): nat
  decreases m + n
{
  if m == 0 || n == 0 then 0
  else if m == 1 || n == 1 then 1
  else Paths(m - 1, n) + Paths(m, n - 1)
}

lemma PathsBase1(n: nat)
  requires n > 0
  ensures Paths(1, n) == 1
{}

lemma PathsBase2(m: nat)
  requires m > 0
  ensures Paths(m, 1) == 1
  decreases m
{
  if m > 1 {
    PathsBase2(m - 1);
  }
}

method UniquePaths(m: nat, n: nat) returns (result: nat)
  requires m > 0 && n > 0
  ensures result == Paths(m, n)
{
  var dp := seq(n, j => 1);
  var i := 1;

  // Initially dp[j] == Paths(1, j+1) for all j
  forall j | 0 <= j < n
    ensures dp[j] == Paths(1, j + 1)
  {
    PathsBase1(j + 1);
  }

  while i < m
    invariant 1 <= i <= m
    invariant |dp| == n
    invariant forall j :: 0 <= j < n ==> dp[j] == Paths(i, j + 1)
    decreases m - i
  {
    var j := 1;
    // dp[0] stays 1 = Paths(i+1, 1)
    PathsBase2(i + 1);
    assert dp[0] == Paths(i, 1) == 1 == Paths(i + 1, 1);

    while j < n
      invariant 1 <= j <= n
      invariant |dp| == n
      invariant dp[0] == Paths(i + 1, 1)
      invariant forall k :: 1 <= k < j ==> dp[k] == Paths(i + 1, k + 1)
      invariant forall k :: j <= k < n ==> dp[k] == Paths(i, k + 1)
      decreases n - j
    {
      // dp[j] == Paths(i, j+1), dp[j-1] == Paths(i+1, j)
      // Paths(i+1, j+1) == Paths(i, j+1) + Paths(i+1, j) == dp[j] + dp[j-1]
      assert dp[j-1] == Paths(i + 1, j);
      assert dp[j] == Paths(i, j + 1);
      dp := dp[..j] + [dp[j] + dp[j-1]] + dp[j+1..];
      j := j + 1;
    }
    i := i + 1;
  }
  result := dp[n - 1];
}
