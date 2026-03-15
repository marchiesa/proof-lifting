// Minimum Cost Climbing Stairs -- Reference solution with invariants

function Min(a: int, b: int): int { if a <= b then a else b }

function MinCost(cost: seq<int>, n: int): int
  requires 0 <= n <= |cost|
  requires forall i :: 0 <= i < |cost| ==> cost[i] >= 0
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 0
  else Min(MinCost(cost, n-1) + cost[n-1], MinCost(cost, n-2) + cost[n-2])
}

method MinCostClimb(cost: seq<int>) returns (result: int)
  requires |cost| >= 2
  requires forall i :: 0 <= i < |cost| ==> cost[i] >= 0
  ensures result == MinCost(cost, |cost|)
{
  var prev2 := 0;
  var prev1 := 0;
  var i := 2;
  while i <= |cost|
    invariant 2 <= i <= |cost| + 1
    invariant prev2 == MinCost(cost, i - 2)
    invariant prev1 == MinCost(cost, i - 1)
    decreases |cost| + 1 - i
  {
    var curr := Min(prev1 + cost[i-1], prev2 + cost[i-2]);
    prev2 := prev1;
    prev1 := curr;
    i := i + 1;
  }
  result := prev1;
}
