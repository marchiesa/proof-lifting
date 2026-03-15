// Optimal BST Cost
// Task: Add loop invariants so that Dafny can verify this program.
// Computes weighted access cost for a degenerate left-skewed BST.

function SumFreq(freq: seq<int>, i: int, j: int): int
  requires 0 <= i <= j <= |freq|
  decreases j - i
{
  if i == j then 0
  else freq[i] + SumFreq(freq, i + 1, j)
}

lemma SumFreqNonNeg(freq: seq<int>, i: int, j: int)
  requires 0 <= i <= j <= |freq|
  requires forall k :: 0 <= k < |freq| ==> freq[k] >= 0
  ensures SumFreq(freq, i, j) >= 0
  decreases j - i
{
  if i < j { SumFreqNonNeg(freq, i + 1, j); }
}

method OptimalBSTCost(freq: seq<int>) returns (cost: int)
  requires |freq| > 0
  requires forall i :: 0 <= i < |freq| ==> freq[i] >= 0
  ensures cost >= 0
{
  cost := 0;
  var depth := 1;
  var i := 0;
  while i < |freq|
    // invariant
  {
    cost := cost + freq[i] * depth;
    depth := depth + 1;
    i := i + 1;
  }
}
