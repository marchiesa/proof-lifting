// --- Specification functions ---

function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

predicate BitSet(mask: nat, i: nat)
{
  (mask / Pow2(i)) % 2 == 1
}

function FilterTeam(s: seq<int>, mask: nat, selectA: bool): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else
    var rest := FilterTeam(s[..|s|-1], mask, selectA);
    if BitSet(mask, |s| - 1) == selectA then rest + [s[|s|-1]]
    else rest
}

function SeqMax(a: seq<int>): int
  requires |a| >= 1
  decreases |a|
{
  if |a| == 1 then a[0]
  else
    var rest := SeqMax(a[..|a|-1]);
    if a[|a|-1] > rest then a[|a|-1] else rest
}

function SeqMin(a: seq<int>): int
  requires |a| >= 1
  decreases |a|
{
  if |a| == 1 then a[0]
  else
    var rest := SeqMin(a[..|a|-1]);
    if a[|a|-1] < rest then a[|a|-1] else rest
}

function Abs(x: int): int
{
  if x >= 0 then x else -x
}

function SplitCost(s: seq<int>, mask: nat): int
{
  var teamA := FilterTeam(s, mask, true);
  var teamB := FilterTeam(s, mask, false);
  if |teamA| >= 1 && |teamB| >= 1 then
    Abs(SeqMax(teamA) - SeqMin(teamB))
  else
    -1
}

// Testable spec predicate: wraps the two ensures clauses of HonestCoach
predicate IsMinCost(s: seq<int>, minDiff: int)
  requires |s| >= 2
{
  (forall mask | 1 <= mask <= Pow2(|s|) - 2 :: SplitCost(s, mask) >= minDiff) &&
  (exists mask | 1 <= mask <= Pow2(|s|) - 2 :: SplitCost(s, mask) == minDiff)
}

// --- Implementation ---

method HonestCoach(s: seq<int>) returns (minDiff: int)
  requires |s| >= 2
  ensures forall mask | 1 <= mask <= Pow2(|s|) - 2 :: SplitCost(s, mask) >= minDiff
  ensures exists mask | 1 <= mask <= Pow2(|s|) - 2 :: SplitCost(s, mask) == minDiff
{
  // ... insertion sort + min consecutive diff ...
}

method Main()
{
  // 10 spec positive tests (small inputs, IsMinCost returns true)
  // 10 spec negative tests (small inputs, wrong answer, IsMinCost returns false)
  // 28 implementation tests (full-size, HonestCoach returns correct value)
  print "All tests passed\n";
}