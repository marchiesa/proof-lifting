// Minimum Cost to Merge Stones -- Reference solution with invariants
// Simplified: compute total pairwise merge cost greedily (sum of prefix sums)

function SumRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + SumRange(a, lo + 1, hi)
}

lemma SumRangeNonNeg(a: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |a|
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures SumRange(a, lo, hi) >= 0
  decreases hi - lo
{
  if lo < hi { SumRangeNonNeg(a, lo + 1, hi); }
}

// Computes cumulative merge cost: sum of all prefix sums
// This equals the cost of always merging the first two piles
method MinCostMerge(stones: seq<int>) returns (cost: int)
  requires |stones| >= 1
  requires forall i :: 0 <= i < |stones| ==> stones[i] >= 0
  ensures cost >= 0
  ensures |stones| == 1 ==> cost == 0
{
  if |stones| == 1 { return 0; }
  var n := |stones|;

  // Build prefix sums
  var ps := new int[n + 1];
  ps[0] := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant ps[0] == 0
    invariant forall k :: 0 <= k <= i ==> ps[k] >= 0
    decreases n - i
  {
    ps[i + 1] := ps[i] + stones[i];
    i := i + 1;
  }

  // Cost = sum of ps[2..n+1]  (each merge adds the running total)
  cost := 0;
  i := 2;
  while i <= n
    invariant 2 <= i <= n + 1
    invariant cost >= 0
    decreases n + 1 - i
  {
    cost := cost + ps[i];
    i := i + 1;
  }
}
