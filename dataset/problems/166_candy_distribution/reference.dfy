// Candy Distribution -- Reference solution with invariants

function Max(a: int, b: int): int { if a >= b then a else b }

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

  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant |candy| == n
    invariant forall k :: 0 <= k < n ==> candy[k] >= 1
    invariant forall k :: 0 < k < i && ratings[k] > ratings[k-1] ==> candy[k] > candy[k-1]
    decreases n - i
  {
    if ratings[i] > ratings[i-1] {
      candy := candy[i := candy[i-1] + 1];
    }
    i := i + 1;
  }

  i := n - 2;
  while i >= 0
    invariant -1 <= i < n - 1
    invariant |candy| == n
    invariant forall k :: 0 <= k < n ==> candy[k] >= 1
    invariant forall k :: 0 < k < n && ratings[k] > ratings[k-1] ==> candy[k] > candy[k-1]
    invariant forall k :: i < k < n - 1 && ratings[k] > ratings[k+1] ==> candy[k] > candy[k+1]
    decreases i + 1
  {
    if ratings[i] > ratings[i+1] {
      candy := candy[i := Max(candy[i], candy[i+1] + 1)];
    }
    i := i - 1;
  }

  total := 0;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant total >= i
    decreases n - i
  {
    total := total + candy[i];
    i := i + 1;
  }
}
