const NUM_PAIRS: nat := 500000000

function ReplaceVal(v: int, from: int, to: int): int
{
  if v == from then to else v
}

function ApplyPairToVal(v: int, k: nat): int
  requires k >= 1
{
  ReplaceVal(ReplaceVal(v, 2 * k - 1, 2 * k), 2 * k, 2 * k - 1)
}

function ApplyPairsRange(v: int, lo: nat, hi: nat): int
  requires 1 <= lo <= hi
  decreases hi - lo
{
  if v < 2 * lo - 1 || v > 2 * hi then
    v
  else if lo == hi then
    ApplyPairToVal(v, lo)
  else
    var mid := lo + (hi - lo) / 2;
    ApplyPairsRange(ApplyPairsRange(v, lo, mid), mid + 1, hi)
}

function MishkaAlgorithm(v: int): int
  requires 1 <= v <= 2 * NUM_PAIRS
{
  ApplyPairsRange(v, 1, NUM_PAIRS)
}

predicate IsCorrectResult(a: seq<int>, b: seq<int>)
  requires forall i | 0 <= i < |a| :: 1 <= a[i] <= 1000000000
{
  |b| == |a| &&
  forall i | 0 <= i < |a| :: b[i] == MishkaAlgorithm(a[i])
}

method AdjacentReplacements(a: seq<int>) returns (b: seq<int>)
  requires forall i | 0 <= i < |a| :: 1 <= a[i] <= 1000000000
  ensures IsCorrectResult(a, b)
{
  b := [];
  for i := 0 to |a| {
    if a[i] % 2 == 0 {
      b := b + [a[i] - 1];
    } else {
      b := b + [a[i]];
    }
  }
}

method Main()
{
  var result: seq<int>;

  // === SPEC POSITIVE TESTS ===
  // IsCorrectResult with small inputs (values 1-5, length 1-3)

  // Spec positive 1 (from test 3: odd single stays same)
  expect IsCorrectResult([1], [1]), "spec positive 1";

  // Spec positive 2 (from test 4: even single decrements)
  expect IsCorrectResult([2], [1]), "spec positive 2";

  // Spec positive 3 (from test 7: odd single stays same)
  expect IsCorrectResult([3], [3]), "spec positive 3";

  // Spec positive 4 (from test 5: even single decrements)
  expect IsCorrectResult([4], [3]), "spec positive 4";

  // Spec positive 5 (from test 3: odd single stays same)
  expect IsCorrectResult([5], [5]), "spec positive 5";

  // Spec positive 6 (from test 8: even pair)
  expect IsCorrectResult([2, 2], [1, 1]), "spec positive 6";

  // Spec positive 7 (from test 9: even triple)
  expect IsCorrectResult([2, 2, 2], [1, 1, 1]), "spec positive 7";

  // Spec positive 8 (from test 10: even pair)
  expect IsCorrectResult([4, 4], [3, 3]), "spec positive 8";

  // Spec positive 9 (from test 1: mixed sequence scaled down)
  expect IsCorrectResult([1, 2, 4], [1, 1, 3]), "spec positive 9";

  // Spec positive 10 (from test 2: mixed sequence scaled down)
  expect IsCorrectResult([1, 5, 2], [1, 5, 1]), "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // IsCorrectResult must reject wrong outputs

  // Spec negative 1 (from neg 1: first element wrong in mixed)
  expect !IsCorrectResult([1, 2, 4], [2, 1, 3]), "spec negative 1";

  // Spec negative 2 (from neg 2: first element not decremented)
  expect !IsCorrectResult([2, 1], [2, 1]), "spec negative 2";

  // Spec negative 3 (from neg 3: odd value incremented)
  expect !IsCorrectResult([1], [2]), "spec negative 3";

  // Spec negative 4 (from neg 4: even not decremented)
  expect !IsCorrectResult([2], [2]), "spec negative 4";

  // Spec negative 5 (from neg 5: even not decremented)
  expect !IsCorrectResult([4], [4]), "spec negative 5";

  // Spec negative 6 (from neg 6: first wrong in repeated even, scaled down)
  expect !IsCorrectResult([4, 4, 4], [4, 3, 3]), "spec negative 6";

  // Spec negative 7 (from neg 7: odd value incremented)
  expect !IsCorrectResult([3], [4]), "spec negative 7";

  // Spec negative 8 (from neg 8: first element wrong)
  expect !IsCorrectResult([2, 2], [2, 1]), "spec negative 8";

  // Spec negative 9 (from neg 9: first element wrong)
  expect !IsCorrectResult([2, 2, 2], [2, 1, 1]), "spec negative 9";

  // Spec negative 10 (from neg 10: first element wrong)
  expect !IsCorrectResult([4, 4], [4, 3]), "spec negative 10";

  // === IMPLEMENTATION TESTS ===

  // Impl test 1
  result := AdjacentReplacements([1, 2, 4, 5, 10]);
  expect result == [1, 1, 3, 5, 9], "impl test 1 failed";

  // Impl test 2
  result := AdjacentReplacements([10000, 10, 50605065, 1, 5, 89, 5, 999999999, 60506056, 1000000000]);
  expect result == [9999, 9, 50605065, 1, 5, 89, 5, 999999999, 60506055, 999999999], "impl test 2 failed";

  // Impl test 3
  result := AdjacentReplacements([999999999]);
  expect result == [999999999], "impl test 3 failed";

  // Impl test 4
  result := AdjacentReplacements([1000000000]);
  expect result == [999999999], "impl test 4 failed";

  // Impl test 5
  result := AdjacentReplacements([210400]);
  expect result == [210399], "impl test 5 failed";

  // Impl test 6
  result := AdjacentReplacements([100000000, 100000000, 100000000, 100000000, 100000000]);
  expect result == [99999999, 99999999, 99999999, 99999999, 99999999], "impl test 6 failed";

  // Impl test 7
  result := AdjacentReplacements([2441139]);
  expect result == [2441139], "impl test 7 failed";

  // Impl test 8
  result := AdjacentReplacements([2, 2]);
  expect result == [1, 1], "impl test 8 failed";

  // Impl test 9
  result := AdjacentReplacements([2, 2, 2]);
  expect result == [1, 1, 1], "impl test 9 failed";

  // Impl test 10
  result := AdjacentReplacements([4, 4]);
  expect result == [3, 3], "impl test 10 failed";

  print "All tests passed\n";
}