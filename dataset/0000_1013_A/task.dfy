ghost function Sum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s|-1]) + s[|s|-1]
}

ghost predicate AllNonNeg(s: seq<int>)
{
  forall i | 0 <= i < |s| :: s[i] >= 0
}

// A single legal operation by one jury member on the stone piles.
// A jury member either takes one stone from a pile (removes it from the garden)
// or moves one stone from one pile to another.
ghost predicate LegalStep(before: seq<int>, after: seq<int>)
{
  |before| == |after| &&
  (
    // Take one stone from pile i
    (exists i | 0 <= i < |before| ::
      before[i] > 0 &&
      after == before[i := before[i] - 1])
    ||
    // Move one stone from pile i to pile j
    (exists i | 0 <= i < |before| ::
      exists j | 0 <= j < |before| ::
        i != j &&
        before[i] > 0 &&
        after == before[i := before[i] - 1][j := before[j] + 1])
  )
}

// A valid transformation path: a sequence of configurations where each
// consecutive pair is related by a LegalStep.
ghost predicate IsValidPath(path: seq<seq<int>>)
{
  |path| >= 1 &&
  (forall k | 0 <= k < |path| - 1 :: LegalStep(path[k], path[k + 1]))
}

// A valid removal vector: kept[i] stones remain in pile i after jury members
// take stones, with 0 <= kept[i] <= x[i] for each pile, and the total kept
// equals targetSum. The kept stones can then be freely redistributed via
// move operations to achieve any target configuration with that same total.
ghost predicate ValidRemoval(x: seq<int>, kept: seq<int>, targetSum: int)
{
  |kept| == |x| &&
  (forall i | 0 <= i < |x| :: 0 <= kept[i] <= x[i]) &&
  Sum(kept) == targetSum
}

// Constructive witness for a valid removal: greedily keep as many stones
// as possible from each pile (left to right) until the target is met.
ghost function GreedyKeep(x: seq<int>, remaining: int): seq<int>
  decreases |x|
{
  if |x| == 0 then []
  else
    var keep := if remaining <= 0 then 0
                else if remaining >= x[0] then x[0]
                else remaining;
    [keep] + GreedyKeep(x[1..], remaining - keep)
}

// The transformation from x to y is possible iff there exists a valid
// removal from x whose remaining total equals Sum(y). This is equivalent
// to the existence of a path of LegalSteps from x to y, because:
// (1) After removal, the kept stones can always be redistributed via
//     move operations to match any target y with the same total.
// (2) Conversely, any sequence of take/move operations can only decrease
//     or preserve the total, so Sum(y) <= Sum(x) is necessary.
// GreedyKeep constructs such a removal witness when one exists.
ghost predicate CanTransform(x: seq<int>, y: seq<int>)
{
  |x| == |y| &&
  AllNonNeg(x) &&
  AllNonNeg(y) &&
  ValidRemoval(x, GreedyKeep(x, Sum(y)), Sum(y))
}

method PilesWithStones(x: seq<int>, y: seq<int>) returns (result: bool)
  requires |x| == |y|
  requires AllNonNeg(x)
  requires AllNonNeg(y)
  ensures result == CanTransform(x, y)
{
  var xSum := 0;
  var i := 0;
  while i < |x|
  {
    xSum := xSum + x[i];
    i := i + 1;
  }
  var ySum := 0;
  i := 0;
  while i < |y|
  {
    ySum := ySum + y[i];
    i := i + 1;
  }
  result := ySum <= xSum;
}