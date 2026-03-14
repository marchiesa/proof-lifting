// Problem 1: 0/1 Knapsack with Optimality Proof
//
// Given items with weights and values, and a capacity W,
// find the maximum total value achievable by selecting a subset
// of items whose total weight does not exceed W.
//
// The spec requires OPTIMALITY: no valid subset achieves higher value.

// A "subset" of items 0..n-1 is represented as a set of indices
ghost predicate ValidSubset(items: nat, subset: set<nat>)
{
  forall i :: i in subset ==> i < items
}

// Total weight of a subset of items
ghost function SubsetWeight(weights: seq<nat>, subset: set<nat>): nat
  requires forall i :: i in subset ==> i < |weights|
  decreases subset
{
  if subset == {} then 0
  else
    var x := SetMin(subset);
    weights[x] + SubsetWeight(weights, subset - {x})
}

// Total value of a subset of items
ghost function SubsetValue(values: seq<nat>, subset: set<nat>): nat
  requires forall i :: i in subset ==> i < |values|
  decreases subset
{
  if subset == {} then 0
  else
    var x := SetMin(subset);
    values[x] + SubsetValue(values, subset - {x})
}

// Helper: minimum element of a non-empty set of naturals
ghost function SetMin(s: set<nat>): nat
  requires s != {}
  ensures SetMin(s) in s
  ensures forall x :: x in s ==> SetMin(s) <= x
{
  var x :| x in s;
  if s == {x} then x
  else
    var rest := s - {x};
    var minRest := SetMin(rest);
    if x <= minRest then x else minRest
}

// A subset is feasible if its total weight is within capacity
ghost predicate FeasibleSubset(weights: seq<nat>, capacity: nat, items: nat, subset: set<nat>)
  requires |weights| >= items
  requires forall i :: i in subset ==> i < items
{
  SubsetWeight(weights[..items], subset) <= capacity
}

// The OPTIMALITY spec: the returned value is the maximum over all feasible subsets
// considering only items 0..items-1
ghost predicate IsOptimalValue(
  weights: seq<nat>, values: seq<nat>, capacity: nat, items: nat, optValue: nat)
  requires |weights| >= items && |values| >= items
{
  // 1. There exists a feasible subset achieving optValue
  (exists subset: set<nat> ::
    ValidSubset(items, subset) &&
    FeasibleSubset(weights, capacity, items, subset) &&
    SubsetValue(values[..items], subset) == optValue) &&
  // 2. No feasible subset achieves more than optValue
  (forall subset: set<nat> ::
    ValidSubset(items, subset) &&
    FeasibleSubset(weights, capacity, items, subset) ==>
    SubsetValue(values[..items], subset) <= optValue)
}

// Main method: 0/1 Knapsack via bottom-up DP
// Returns the maximum value achievable
method Knapsack(weights: seq<nat>, values: seq<nat>, W: nat) returns (maxVal: nat)
  requires |weights| == |values|
  requires |weights| > 0
  ensures IsOptimalValue(weights, values, W, |weights|, maxVal)
{
  var n := |weights|;

  // dp[i][w] = max value using items 0..i-1 with capacity w
  var dp := new nat[n + 1, W + 1];

  // Base case: 0 items => 0 value
  var w := 0;
  while w <= W
  {
    dp[0, w] := 0;
    w := w + 1;
  }

  // Fill DP table
  var i := 1;
  while i <= n
  {
    w := 0;
    while w <= W
    {
      if weights[i - 1] <= w {
        dp[i, w] := if dp[i - 1, w] >= dp[i - 1, w - weights[i - 1]] + values[i - 1]
                     then dp[i - 1, w]
                     else dp[i - 1, w - weights[i - 1]] + values[i - 1];
      } else {
        dp[i, w] := dp[i - 1, w];
      }
      w := w + 1;
    }
    i := i + 1;
  }

  maxVal := dp[n, W];
}
