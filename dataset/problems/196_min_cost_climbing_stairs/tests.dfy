// Minimum Cost Climbing Stairs

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
  var prev2 := 0; // MinCost(cost, 0)
  var prev1 := 0; // MinCost(cost, 1)
  var i := 2;
  while i <= |cost|
  {
    var curr := Min(prev1 + cost[i-1], prev2 + cost[i-2]);
    prev2 := prev1;
    prev1 := curr;
    i := i + 1;
  }
  result := prev1;
}

method Main()
{
  // [10, 15, 20] => min(15+20, 10+20) vs ... = 15
  var a := [10, 15, 20];
  var r1 := MinCostClimb(a);
  expect r1 == MinCost(a, |a|);
  expect MinCost(a, 3) == Min(MinCost(a, 2) + 20, MinCost(a, 1) + 15);
  expect r1 == 15;

  // [1, 100, 1, 1, 1, 100, 1, 1, 100, 1]
  var b := [1, 100, 1, 1, 1, 100, 1, 1, 100, 1];
  var r2 := MinCostClimb(b);
  expect r2 == MinCost(b, |b|);
  expect r2 == 6;

  // Two steps
  var c := [5, 10];
  var r3 := MinCostClimb(c);
  expect r3 == MinCost(c, 2);
  expect r3 == Min(0 + 10, 0 + 5);
  expect r3 == 5;

  print "All spec tests passed\n";
}
