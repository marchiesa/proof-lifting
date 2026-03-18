// --- Specification: model the problem's partition structure ---

ghost function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

ghost predicate BitSet(mask: nat, i: nat)
{
  (mask / Pow2(i)) % 2 == 1
}

// Extract the sub-sequence of athletes assigned to team A (selectA=true) or team B (selectA=false)
ghost function FilterTeam(s: seq<int>, mask: nat, selectA: bool): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else
    var rest := FilterTeam(s[..|s|-1], mask, selectA);
    if BitSet(mask, |s| - 1) == selectA then rest + [s[|s|-1]]
    else rest
}

ghost function SeqMax(a: seq<int>): int
  requires |a| >= 1
  decreases |a|
{
  if |a| == 1 then a[0]
  else
    var rest := SeqMax(a[..|a|-1]);
    if a[|a|-1] > rest then a[|a|-1] else rest
}

ghost function SeqMin(a: seq<int>): int
  requires |a| >= 1
  decreases |a|
{
  if |a| == 1 then a[0]
  else
    var rest := SeqMin(a[..|a|-1]);
    if a[|a|-1] < rest then a[|a|-1] else rest
}

ghost function Abs(x: int): int
{
  if x >= 0 then x else -x
}

// Cost of splitting s according to bitmask: |max(teamA) - min(teamB)|
// Returns -1 for degenerate splits (one team empty); valid masks never hit this case.
ghost function SplitCost(s: seq<int>, mask: nat): int
{
  var teamA := FilterTeam(s, mask, true);
  var teamB := FilterTeam(s, mask, false);
  if |teamA| >= 1 && |teamB| >= 1 then
    Abs(SeqMax(teamA) - SeqMin(teamB))
  else
    -1
}

// --- Method with formal specification ---
// A bitmask in [1, 2^n - 2] encodes every partition of n athletes into two non-empty teams:
//   bit i set  => athlete i in team A
//   bit i clear => athlete i in team B
// The result is the minimum |max(A) - min(B)| over all such partitions.

method HonestCoach(s: seq<int>) returns (minDiff: int)
  requires |s| >= 2
  ensures forall mask :: 1 <= mask <= Pow2(|s|) - 2 ==> SplitCost(s, mask) >= minDiff
  ensures exists mask | 1 <= mask <= Pow2(|s|) - 2 :: SplitCost(s, mask) == minDiff
{
  var a := s;
  // Sort (insertion sort)
  var i := 1;
  while i < |a|
  {
    var j := i;
    while j > 0 && a[j-1] > a[j]
    {
      var tmp := a[j-1];
      a := a[j-1 := a[j]][j := tmp];
      j := j - 1;
    }
    i := i + 1;
  }
  // Find minimum consecutive difference
  minDiff := a[1] - a[0];
  i := 2;
  while i < |a|
  {
    var diff := a[i] - a[i-1];
    if diff < minDiff {
      minDiff := diff;
    }
    i := i + 1;
  }
}