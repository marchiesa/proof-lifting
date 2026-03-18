// ============================================================
// Specification for "Nezzar and Colorful Balls"
//
// Optimality is certified via duality:
//   (1) an explicit valid k-coloring   (upper bound), and
//   (2) an explicit clique of size k   (lower bound).
// Together these prove k is the minimum number of colors.
// ============================================================

// The input sequence is non-decreasing (problem constraint).
ghost predicate NonDecreasing(a: seq<int>)
{
  forall i | 0 <= i < |a| - 1 :: a[i] <= a[i + 1]
}

// A valid k-coloring: every ball gets a color in [0..k), and
// for every pair of same-colored balls, their values are
// strictly increasing (left to right).
ghost predicate IsValidColoring(a: seq<int>, coloring: seq<int>, k: int)
{
  |coloring| == |a| &&
  k >= 0 &&
  (forall i | 0 <= i < |coloring| :: 0 <= coloring[i] < k) &&
  (forall i, j | 0 <= i < j < |a| ::
    coloring[i] == coloring[j] ==> a[i] < a[j])
}

// A clique: positions that pairwise conflict — no two can share
// a color. Positions i < j conflict when a[i] >= a[j], since
// placing both in one color group violates strict increase.
// Any valid coloring needs at least |clique| distinct colors.
ghost predicate IsClique(a: seq<int>, positions: seq<int>)
{
  (forall i | 0 <= i < |positions| :: 0 <= positions[i] < |a|) &&
  (forall i, j | 0 <= i < j < |positions| :: positions[i] < positions[j]) &&
  (forall i, j | 0 <= i < j < |positions| :: a[positions[i]] >= a[positions[j]])
}

// ---- Witness-construction helpers ----

// Count occurrences of v in a.
ghost function Freq(a: seq<int>, v: int): int
{
  if |a| == 0 then 0
  else (if a[|a| - 1] == v then 1 else 0) + Freq(a[..|a| - 1], v)
}

// Upper-bound witness: color of position i = number of earlier
// positions with the same value. For a non-decreasing sequence,
// same-colored positions necessarily have strictly increasing values.
ghost function WitnessColoring(a: seq<int>): seq<int>
{
  if |a| == 0 then []
  else WitnessColoring(a[..|a| - 1]) + [Freq(a[..|a| - 1], a[|a| - 1])]
}

// The element from candidates with maximum frequency in a.
ghost function ArgMaxFreq(a: seq<int>, candidates: seq<int>): int
  requires |candidates| > 0
{
  if |candidates| == 1 then candidates[0]
  else
    var best := ArgMaxFreq(a, candidates[..|candidates| - 1]);
    if Freq(a, candidates[|candidates| - 1]) >= Freq(a, best)
    then candidates[|candidates| - 1]
    else best
}

// All indices where a[i] == v, in increasing order.
ghost function PositionsOf(a: seq<int>, v: int): seq<int>
{
  if |a| == 0 then []
  else
    var prev := PositionsOf(a[..|a| - 1], v);
    if a[|a| - 1] == v then prev + [|a| - 1] else prev
}

// Lower-bound witness: the positions of the most frequent
// element form a maximum clique (all pairwise conflicting).
ghost function MaxClique(a: seq<int>): seq<int>
  requires |a| > 0
{
  PositionsOf(a, ArgMaxFreq(a, a))
}

// ============================================================

method MinColors(a: seq<int>) returns (result: int)
  requires NonDecreasing(a)
  // Upper bound: a valid coloring with 'result' colors exists.
  ensures IsValidColoring(a, WitnessColoring(a), result)
  // Lower bound: a clique of size 'result' exists, proving no
  // coloring with fewer colors can be valid.
  ensures |a| > 0 ==> IsClique(a, MaxClique(a)) && |MaxClique(a)| == result
  ensures |a| == 0 ==> result == 0
{
  var freq: map<int, int> := map[];
  for i := 0 to |a| {
    var key := a[i];
    if key in freq {
      freq := freq[key := freq[key] + 1];
    } else {
      freq := freq[key := 1];
    }
  }
  result := 0;
  var keys := freq.Keys;
  while keys != {}
    decreases keys
  {
    var k :| k in keys;
    if freq[k] > result {
      result := freq[k];
    }
    keys := keys - {k};
  }
}