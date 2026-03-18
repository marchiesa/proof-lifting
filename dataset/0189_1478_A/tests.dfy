// ============================================================
// Specification predicates and functions
// ============================================================

predicate NonDecreasing(a: seq<int>)
{
  forall i | 0 <= i < |a| - 1 :: a[i] <= a[i + 1]
}

predicate IsValidColoring(a: seq<int>, coloring: seq<int>, k: int)
{
  |coloring| == |a| &&
  k >= 0 &&
  (forall i | 0 <= i < |coloring| :: 0 <= coloring[i] < k) &&
  (forall i, j | 0 <= i < j < |a| ::
    coloring[i] == coloring[j] ==> a[i] < a[j])
}

predicate IsClique(a: seq<int>, positions: seq<int>)
{
  (forall i | 0 <= i < |positions| :: 0 <= positions[i] < |a|) &&
  (forall i, j | 0 <= i < j < |positions| :: positions[i] < positions[j]) &&
  (forall i, j | 0 <= i < j < |positions| :: a[positions[i]] >= a[positions[j]])
}

function Freq(a: seq<int>, v: int): int
{
  if |a| == 0 then 0
  else (if a[|a| - 1] == v then 1 else 0) + Freq(a[..|a| - 1], v)
}

function WitnessColoring(a: seq<int>): seq<int>
{
  if |a| == 0 then []
  else WitnessColoring(a[..|a| - 1]) + [Freq(a[..|a| - 1], a[|a| - 1])]
}

function ArgMaxFreq(a: seq<int>, candidates: seq<int>): int
  requires |candidates| > 0
{
  if |candidates| == 1 then candidates[0]
  else
    var best := ArgMaxFreq(a, candidates[..|candidates| - 1]);
    if Freq(a, candidates[|candidates| - 1]) >= Freq(a, best)
    then candidates[|candidates| - 1]
    else best
}

function PositionsOf(a: seq<int>, v: int): seq<int>
{
  if |a| == 0 then []
  else
    var prev := PositionsOf(a[..|a| - 1], v);
    if a[|a| - 1] == v then prev + [|a| - 1] else prev
}

function MaxClique(a: seq<int>): seq<int>
  requires |a| > 0
{
  PositionsOf(a, ArgMaxFreq(a, a))
}

// Combined ensures predicate for spec testing
predicate MeetsSpec(a: seq<int>, result: int)
  requires |a| > 0
{
  IsValidColoring(a, WitnessColoring(a), result) &&
  IsClique(a, MaxClique(a)) &&
  |MaxClique(a)| == result
}

// ============================================================
// Implementation
// ============================================================

method MinColors(a: seq<int>) returns (result: int)
  requires NonDecreasing(a)
  ensures IsValidColoring(a, WitnessColoring(a), result)
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

// ============================================================
// Tests
// ============================================================

method Main()
{
  // ========== SPEC POSITIVE TESTS (small inputs, length 1-3) ==========
  // Each maps from a positive test pair, scaled down to small size.
  expect MeetsSpec([1], 1), "spec positive 1";                 // from test 1e/6
  expect MeetsSpec([1, 2], 1), "spec positive 2";              // from test 2b
  expect MeetsSpec([1, 1, 1], 3), "spec positive 3";           // from test 2c/7
  expect MeetsSpec([1, 2, 3], 1), "spec positive 4";           // from test 1d/7
  expect MeetsSpec([1, 1], 2), "spec positive 5";              // from test 5 scaled
  expect MeetsSpec([2, 2, 2], 3), "spec positive 6";           // from test 1c scaled
  expect MeetsSpec([1, 1, 2], 2), "spec positive 7";           // from test 3 scaled

  // ========== SPEC NEGATIVE TESTS (small inputs, wrong outputs) ==========
  // Each maps from a negative test pair, scaled down to small size.
  expect !MeetsSpec([1, 1, 1], 4), "spec negative 1";          // neg1: correct=3, wrong=4
  expect !MeetsSpec([1], 2), "spec negative 2";                // neg2: correct=1, wrong=2
  expect !MeetsSpec([1, 1, 2], 3), "spec negative 3";          // neg3: correct=2, wrong=3
  expect !MeetsSpec([1, 2, 3], 2), "spec negative 4";          // neg4: correct=1, wrong=2
  expect !MeetsSpec([1, 1], 3), "spec negative 5";             // neg5: correct=2, wrong=3
  expect !MeetsSpec([1], 2), "spec negative 6";                // neg6: correct=1, wrong=2
  expect !MeetsSpec([1, 1, 1], 4), "spec negative 7";          // neg7: correct=3, wrong=4
  expect !MeetsSpec([2, 2, 2], 4), "spec negative 8";          // neg8: correct=3, wrong=4
  expect !MeetsSpec([1, 1, 1], 5), "spec negative 9";          // neg9: correct=3, wrong=5
  expect !MeetsSpec([1, 2], 2), "spec negative 10";            // neg10: correct=1, wrong=2

  // ========== IMPLEMENTATION TESTS (full-size inputs) ==========
  var r: int;

  r := MinColors([1, 1, 1, 2, 3, 4]);
  expect r == 3, "impl test 1a failed";

  r := MinColors([1, 1, 2, 2, 3]);
  expect r == 2, "impl test 1b failed";

  r := MinColors([2, 2, 2, 2]);
  expect r == 4, "impl test 1c failed";

  r := MinColors([1, 2, 3]);
  expect r == 1, "impl test 1d failed";

  r := MinColors([1]);
  expect r == 1, "impl test 1e failed";

  r := MinColors([1, 2]);
  expect r == 1, "impl test 2b failed";

  r := MinColors([1, 1, 1]);
  expect r == 3, "impl test 2c failed";

  r := MinColors([1, 1, 2, 3, 3]);
  expect r == 2, "impl test 3 failed";

  r := MinColors([1, 2, 3, 4]);
  expect r == 1, "impl test 4a failed";

  r := MinColors([1, 1, 1, 2, 2, 3]);
  expect r == 3, "impl test 4b failed";

  r := MinColors([1, 1, 2, 2, 3, 3, 4, 4, 5, 5]);
  expect r == 2, "impl test 5 failed";

  r := MinColors([1, 2, 2, 2, 3, 4, 4]);
  expect r == 3, "impl test 8 failed";

  r := MinColors([1, 1, 1, 1, 1, 1, 1, 1]);
  expect r == 8, "impl test 9 failed";

  r := MinColors([1, 2, 3, 4, 5]);
  expect r == 1, "impl test 10a failed";

  r := MinColors([1, 1, 2, 2]);
  expect r == 2, "impl test 10b failed";

  r := MinColors([1, 1, 2, 3, 3, 3]);
  expect r == 3, "impl test 10c failed";

  r := MinColors([1, 1, 1, 2, 3, 3, 4, 5, 5, 5]);
  expect r == 3, "impl test 11 failed";

  print "All tests passed\n";
}