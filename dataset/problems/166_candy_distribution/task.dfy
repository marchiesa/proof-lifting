// Candy Distribution
// Task: Add loop invariants so that Dafny can verify this program.

function Max(a: int, b: int): int { if a >= b then a else b }

function SumArray(a: seq<int>): int {
  if |a| == 0 then 0 else a[0] + SumArray(a[1..])
}

// Each child gets >= 1 candy, and more than any neighbor with lower rating
predicate ValidDistribution(ratings: seq<int>, candy: seq<int>) {
  |candy| == |ratings| &&
  (forall i :: 0 <= i < |candy| ==> candy[i] >= 1) &&
  (forall i :: 0 < i < |ratings| && ratings[i] > ratings[i-1] ==> candy[i] > candy[i-1]) &&
  (forall i :: 0 <= i < |ratings| - 1 && ratings[i] > ratings[i+1] ==> candy[i] > candy[i+1])
}

method CandyDistribution(ratings: seq<int>) returns (candy: seq<int>, total: int)
  requires |ratings| > 0
  ensures ValidDistribution(ratings, candy)
  ensures total >= |ratings|
{
  var n := |ratings|;
  candy := seq(n, _ => 1);

  // Left to right pass
  var i := 1;
  while i < n
  {
    if ratings[i] > ratings[i-1] {
      candy := candy[i := candy[i-1] + 1];
    }
    i := i + 1;
  }

  // Right to left pass
  i := n - 2;
  while i >= 0
  {
    if ratings[i] > ratings[i+1] {
      candy := candy[i := Max(candy[i], candy[i+1] + 1)];
    }
    i := i - 1;
  }

  // Sum
  total := 0;
  i := 0;
  while i < n
  {
    total := total + candy[i];
    i := i + 1;
  }
}
