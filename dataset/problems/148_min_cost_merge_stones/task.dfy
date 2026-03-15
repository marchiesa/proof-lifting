// Minimum Cost to Merge Stones
// Task: Add loop invariants so that Dafny can verify this program.
// Computes cumulative merge cost using prefix sums.

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

method MinCostMerge(stones: seq<int>) returns (cost: int)
  requires |stones| >= 1
  requires forall i :: 0 <= i < |stones| ==> stones[i] >= 0
  ensures cost >= 0
  ensures |stones| == 1 ==> cost == 0
{
  if |stones| == 1 { return 0; }
  var n := |stones|;

  var ps := new int[n + 1];
  ps[0] := 0;
  var i := 0;
  while i < n
    // invariant
  {
    ps[i + 1] := ps[i] + stones[i];
    i := i + 1;
  }

  cost := 0;
  i := 2;
  while i <= n
    // invariant
  {
    cost := cost + ps[i];
    i := i + 1;
  }
}
