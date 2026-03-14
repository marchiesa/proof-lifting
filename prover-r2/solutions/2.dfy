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

// =====================================================================
// Helper lemmas
// =====================================================================
lemma SubseqDecompose(a: seq<int>, indices: seq<nat>)
  requires |indices| > 1
  requires IsIncreasingSubseq(a, indices)
  ensures IsIncreasingSubseq(a, indices[..|indices|-1])
  ensures indices[|indices|-2] < indices[|indices|-1]
  ensures a[indices[|indices|-2]] < a[indices[|indices|-1]]
{
  var prefix := indices[..|indices|-1];
  assert forall k :: 0 <= k < |prefix| ==> prefix[k] == indices[k];
}

lemma SubseqExtend(a: seq<int>, prefix: seq<nat>, newIdx: nat)
  requires IsIncreasingSubseq(a, prefix)
  requires newIdx < |a|
  requires |prefix| > 0 ==> prefix[|prefix|-1] < newIdx
  requires |prefix| > 0 ==> a[prefix[|prefix|-1]] < a[newIdx]
  ensures IsIncreasingSubseq(a, prefix + [newIdx])
{
  var ext := prefix + [newIdx];
  forall j, k | 0 <= j < k < |ext|
    ensures ext[j] < ext[k]
  {
    if k < |prefix| {
    } else if j < |prefix| - 1 {
      assert prefix[j] < prefix[|prefix|-1];
    }
  }
  forall j, k | 0 <= j < k < |ext|
    ensures a[ext[j]] < a[ext[k]]
  {
    if k < |prefix| {
    } else if j < |prefix| - 1 {
      assert a[prefix[j]] < a[prefix[|prefix|-1]];
    }
  }
}

// Upper bound lemma
lemma UpperBoundLemma(a: seq<int>, dpVals: seq<nat>, i: nat, idxs: seq<nat>)
  requires i < |a| && |dpVals| > i
  requires forall j :: 0 <= j < i && j < |dpVals| ==>
    (forall is2: seq<nat> :: IsIncreasingSubseqEndingAt(a, is2, j) ==> |is2| <= dpVals[j])
  requires dpVals[i] >= 1
  requires forall j :: 0 <= j < i && a[j] < a[i] && j < |dpVals| ==> dpVals[j] + 1 <= dpVals[i]
  requires IsIncreasingSubseqEndingAt(a, idxs, i)
  ensures |idxs| <= dpVals[i]
{
  if |idxs| > 1 {
    SubseqDecompose(a, idxs);
    var prefix := idxs[..|idxs|-1];
    var j := idxs[|idxs|-2];
    assert IsIncreasingSubseqEndingAt(a, prefix, j);
  }
}

// Singleton IS
lemma SingletonIS(a: seq<int>, i: nat)
  requires i < |a|
  ensures IsIncreasingSubseq(a, [i])
  ensures IsIncreasingSubseqEndingAt(a, [i], i)
{
  var s: seq<nat> := [i];
  assert forall k :: 0 <= k < |s| ==> s[k] < |a|;
}

// IS ending at 0 must have length 1
lemma ISEndingAt0HasLen1(a: seq<int>, idxs: seq<nat>)
  requires |a| > 0
  requires IsIncreasingSubseqEndingAt(a, idxs, 0)
  ensures |idxs| == 1
{
  if |idxs| > 1 {
    assert idxs[|idxs|-2] < idxs[|idxs|-1] == 0;
  }
}

// =====================================================================
// Process one DP cell: prove IsDPOptimalAt(a, i, dp[i])
// =====================================================================
method ProcessCell(a: seq<int>, dp: array<nat>, i: nat, ghost dpOpt: seq<nat>)
  requires i < |a| && dp.Length == |a|
  requires i > 0
  requires dp[i] == 1
  requires |dpOpt| == i
  requires forall k :: 0 <= k < i ==> dp[k] == dpOpt[k]
  requires forall k :: 0 <= k < i ==> IsDPOptimalAt(a, k, dpOpt[k])
  modifies dp
  ensures dp[i] >= 1
  ensures forall k :: 0 <= k < i ==> dp[k] == dpOpt[k]
  ensures forall k :: i < k < dp.Length ==> dp[k] == old(dp[k])
  ensures IsDPOptimalAt(a, i, dp[i])
{
  ghost var witI: seq<nat> := [i];
  SingletonIS(a, i);

  var j := 0;
  while j < i
    invariant 0 <= j <= i
    invariant dp[i] >= 1
    invariant forall j' :: 0 <= j' < j && a[j'] < a[i] ==> dp[j'] + 1 <= dp[i]
    invariant |witI| == dp[i] && IsIncreasingSubseqEndingAt(a, witI, i)
    invariant forall k :: 0 <= k < i ==> dp[k] == dpOpt[k]
    invariant forall k :: i < k < dp.Length ==> dp[k] == old(dp[k])
  {
    if a[j] < a[i] && dp[j] + 1 > dp[i] {
      dp[i] := dp[j] + 1;
      // Need a witness of length dp[j] ending at j
      assert IsDPOptimalAt(a, j, dpOpt[j]);
      assert dp[j] == dpOpt[j];
      ghost var jWit: seq<nat> :| |jWit| == dpOpt[j] && IsIncreasingSubseqEndingAt(a, jWit, j);
      SubseqExtend(a, jWit, i);
      witI := jWit + [i];
    }
    j := j + 1;
  }

  // Prove upper bound
  forall idxs: seq<nat> | IsIncreasingSubseqEndingAt(a, idxs, i)
    ensures |idxs| <= dp[i]
  {
    if |idxs| > 1 {
      SubseqDecompose(a, idxs);
      var prefix := idxs[..|idxs|-1];
      var pred := idxs[|idxs|-2];
      assert pred < i && a[pred] < a[i];
      assert IsIncreasingSubseqEndingAt(a, prefix, pred);
      assert IsDPOptimalAt(a, pred, dpOpt[pred]);
      assert dp[pred] == dpOpt[pred];
    }
  }
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
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> dp[k] == 1
  {
    dp[i] := 1;
    i := i + 1;
  }

  // Prove IsDPOptimalAt for index 0
  SingletonIS(a, 0);
  forall idxs: seq<nat> | IsIncreasingSubseqEndingAt(a, idxs, 0)
    ensures |idxs| <= 1
  {
    ISEndingAt0HasLen1(a, idxs);
  }
  assert IsDPOptimalAt(a, 0, 1);

  ghost var dpOpt: seq<nat> := [dp[0]];

  // Fill DP: dp[i] = 1 + max { dp[j] : j < i and a[j] < a[i] }
  i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant |dpOpt| == i
    invariant forall k :: 0 <= k < i ==> dp[k] == dpOpt[k]
    invariant forall k :: 0 <= k < i ==> IsDPOptimalAt(a, k, dpOpt[k])
    invariant forall k :: i <= k < n ==> dp[k] == 1
    invariant forall k :: 0 <= k < n ==> dp[k] >= 1
  {
    ProcessCell(a, dp, i, dpOpt);
    dpOpt := dpOpt + [dp[i]];
    i := i + 1;
  }

  // Find maximum in dp array
  length := dp[0];
  ghost var maxIdx: nat := 0;
  i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant 0 <= maxIdx < i
    invariant length == dp[maxIdx]
    invariant forall k :: 0 <= k < i ==> dp[k] <= length
  {
    if dp[i] > length {
      length := dp[i];
      maxIdx := i;
    }
    i := i + 1;
  }

  // Prove IsLISLength(a, length)

  // Part 1: existence witness
  assert IsDPOptimalAt(a, maxIdx, dp[maxIdx]);
  ghost var bestWit: seq<nat> :| |bestWit| == dp[maxIdx] && IsIncreasingSubseqEndingAt(a, bestWit, maxIdx);
  assert |bestWit| == length;
  assert IsIncreasingSubseq(a, bestWit);

  // Part 2: optimality
  forall indices: seq<nat> | IsIncreasingSubseq(a, indices)
    ensures |indices| <= length
  {
    if |indices| > 0 {
      var endIdx := indices[|indices|-1];
      assert IsIncreasingSubseqEndingAt(a, indices, endIdx);
      assert endIdx < n;
      assert IsDPOptimalAt(a, endIdx, dp[endIdx]);
    }
  }
}
