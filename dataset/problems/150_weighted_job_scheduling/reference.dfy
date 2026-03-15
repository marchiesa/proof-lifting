// Weighted Job Scheduling -- Reference solution with invariants
// Brute-force O(n * 2^n) style simplified to O(n^2) DP approach

predicate NoOverlap(starts: seq<int>, ends: seq<int>, i: int, j: int)
  requires 0 <= i < |starts| && 0 <= j < |starts|
  requires |starts| == |ends|
{
  ends[i] <= starts[j] || ends[j] <= starts[i]
}

// dp[i] = max profit considering job i as the last job taken
method WeightedJobScheduling(starts: seq<int>, ends: seq<int>, profits: seq<int>) returns (maxProfit: int)
  requires |starts| == |ends| == |profits|
  requires |starts| > 0
  requires forall i :: 0 <= i < |starts| ==> starts[i] <= ends[i]
  requires forall i :: 0 <= i < |profits| ==> profits[i] >= 0
  ensures maxProfit >= 0
  ensures maxProfit >= profits[0]
{
  var n := |starts|;
  var dp := new int[n];

  // Initialize: each job alone
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> dp[k] == profits[k]
    decreases n - i
  {
    dp[i] := profits[i];
    i := i + 1;
  }

  // For each job i, try adding it after compatible job j
  i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant forall k :: 0 <= k < n ==> dp[k] >= profits[k]
    invariant dp[0] >= profits[0]
    decreases n - i
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant dp[i] >= profits[i]
      invariant forall k :: 0 <= k < n ==> dp[k] >= profits[k]
      decreases i - j
    {
      if ends[j] <= starts[i] {
        if dp[j] + profits[i] > dp[i] {
          dp[i] := dp[j] + profits[i];
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }

  // Find maximum in dp
  maxProfit := dp[0];
  i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant maxProfit >= dp[0]
    invariant maxProfit >= profits[0]
    invariant forall k :: 0 <= k < i ==> maxProfit >= dp[k]
    decreases n - i
  {
    if dp[i] > maxProfit {
      maxProfit := dp[i];
    }
    i := i + 1;
  }
}
