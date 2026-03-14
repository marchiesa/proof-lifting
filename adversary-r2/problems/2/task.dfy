// Problem 2: Longest Increasing Subsequence (LIS) with Optimality Proof
//
// Given a sequence of integers, find the length of the longest strictly
// increasing subsequence using O(n^2) DP.
//
// The spec requires OPTIMALITY: no increasing subsequence is longer.

// An increasing subsequence is a sequence of indices where:
// 1. Indices are strictly increasing
// 2. Values at those indices are strictly increasing
ghost predicate IsIncreasingSubseq(a: seq<int>, indices: seq<nat>)
{
  // Indices are valid
  (forall k :: 0 <= k < |indices| ==> indices[k] < |a|) &&
  // Indices are strictly increasing
  (forall j, k :: 0 <= j < k < |indices| ==> indices[j] < indices[k]) &&
  // Values are strictly increasing
  (forall j, k :: 0 <= j < k < |indices| ==> a[indices[j]] < a[indices[k]])
}

// An increasing subsequence that ends at index `endIdx`
ghost predicate IsIncreasingSubseqEndingAt(a: seq<int>, indices: seq<nat>, endIdx: nat)
{
  |indices| > 0 &&
  indices[|indices| - 1] == endIdx &&
  IsIncreasingSubseq(a, indices)
}

// The OPTIMALITY spec for the full LIS problem
ghost predicate IsLISLength(a: seq<int>, length: nat)
{
  // 1. There exists an increasing subsequence of this length
  (exists indices: seq<nat> :: |indices| == length && IsIncreasingSubseq(a, indices)) &&
  // 2. No increasing subsequence is longer
  (forall indices: seq<nat> :: IsIncreasingSubseq(a, indices) ==> |indices| <= length)
}

// Per-cell optimality: dp[i] is the length of the longest increasing
// subsequence ending at index i
ghost predicate IsDPOptimalAt(a: seq<int>, i: nat, dpVal: nat)
  requires i < |a|
{
  // 1. There exists an increasing subsequence of length dpVal ending at i
  (exists indices: seq<nat> ::
    |indices| == dpVal && IsIncreasingSubseqEndingAt(a, indices, i)) &&
  // 2. No increasing subsequence ending at i is longer
  (forall indices: seq<nat> ::
    IsIncreasingSubseqEndingAt(a, indices, i) ==> |indices| <= dpVal)
}

// Main method: LIS via O(n^2) DP
// Returns the length of the longest strictly increasing subsequence
method LIS(a: seq<int>) returns (length: nat)
  requires |a| > 0
  ensures IsLISLength(a, length)
{
  var n := |a|;
  var dp := new nat[n];

  // Base case: every element is an increasing subsequence of length 1
  var i := 0;
  while i < n
  {
    dp[i] := 1;
    i := i + 1;
  }

  // Fill DP: dp[i] = 1 + max { dp[j] : j < i and a[j] < a[i] }
  i := 1;
  while i < n
  {
    var j := 0;
    while j < i
    {
      if a[j] < a[i] && dp[j] + 1 > dp[i] {
        dp[i] := dp[j] + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }

  // Find maximum in dp array
  length := dp[0];
  i := 1;
  while i < n
  {
    if dp[i] > length {
      length := dp[i];
    }
    i := i + 1;
  }
}
