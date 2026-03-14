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
  if s == {x} then
    assert forall y :: y in s ==> y == x;
    x
  else
    var rest := s - {x};
    assert rest != {};
    var minRest := SetMin(rest);
    assert forall y :: y in rest ==> minRest <= y;
    if x <= minRest then
      assert forall y :: y in s ==> (y == x || y in rest);
      x
    else
      assert minRest < x;
      assert forall y :: y in s ==> (y == x || y in rest);
      assert forall y :: y in s ==> minRest <= y;
      minRest
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

// =====================================================================
// Ghost function: optimal value considering items 0..i-1 with capacity w
// This mirrors the DP recurrence exactly.
// =====================================================================
ghost function OptVal(weights: seq<nat>, values: seq<nat>, i: nat, w: nat): nat
  requires i <= |weights| && i <= |values|
  decreases i
{
  if i == 0 then 0
  else if weights[i-1] <= w then
    var excl := OptVal(weights, values, i-1, w);
    var incl := OptVal(weights, values, i-1, w - weights[i-1]) + values[i-1];
    if excl >= incl then excl else incl
  else
    OptVal(weights, values, i-1, w)
}

// =====================================================================
// Lemma: removing an element from a subset and computing weight/value
// =====================================================================
lemma SubsetWeightRemove(weights: seq<nat>, subset: set<nat>, elem: nat)
  requires elem in subset
  requires forall i :: i in subset ==> i < |weights|
  ensures SubsetWeight(weights, subset) == weights[elem] + SubsetWeight(weights, subset - {elem})
  decreases subset
{
  var x := SetMin(subset);
  if x == elem {
    // SubsetWeight unfolds with SetMin(subset) == elem, which is exactly what we need
  } else {
    // x != elem
    var rest := subset - {x};
    assert elem in rest;
    // SubsetWeight(weights, subset) = weights[x] + SubsetWeight(weights, rest)
    SubsetWeightRemove(weights, rest, elem);
    // SubsetWeight(weights, rest) = weights[elem] + SubsetWeight(weights, rest - {elem})
    // So SubsetWeight(weights, subset) = weights[x] + weights[elem] + SubsetWeight(weights, rest - {elem})

    // Now SubsetWeight(weights, subset - {elem}):
    // SetMin(subset - {elem}) should be x since x < elem (SetMin(subset) <= elem and x != elem)
    assert x in (subset - {elem});
    assert SetMin(subset - {elem}) == x by {
      // x is in subset - {elem} and x = SetMin(subset) <= all elements of subset
      // All elements of subset - {elem} are in subset, so x <= all of them
      assert forall y :: y in (subset - {elem}) ==> y in subset;
      assert forall y :: y in (subset - {elem}) ==> x <= y;
    }
    // SubsetWeight(weights, subset - {elem}) = weights[x] + SubsetWeight(weights, (subset - {elem}) - {x})
    assert (subset - {elem}) - {x} == rest - {elem};
  }
}

lemma SubsetValueRemove(values: seq<nat>, subset: set<nat>, elem: nat)
  requires elem in subset
  requires forall i :: i in subset ==> i < |values|
  ensures SubsetValue(values, subset) == values[elem] + SubsetValue(values, subset - {elem})
  decreases subset
{
  var x := SetMin(subset);
  if x == elem {
    // Follows directly from unfolding
  } else {
    var rest := subset - {x};
    assert elem in rest;
    SubsetValueRemove(values, rest, elem);

    assert x in (subset - {elem});
    assert SetMin(subset - {elem}) == x by {
      assert forall y :: y in (subset - {elem}) ==> y in subset;
      assert forall y :: y in (subset - {elem}) ==> x <= y;
    }
    assert (subset - {elem}) - {x} == rest - {elem};
  }
}

// =====================================================================
// Lemma: slice prefix doesn't affect subset weight/value
// =====================================================================
lemma SliceExtendWeight(weights: seq<nat>, items: nat, items2: nat, subset: set<nat>)
  requires items <= items2 <= |weights|
  requires forall i :: i in subset ==> i < items
  ensures SubsetWeight(weights[..items], subset) == SubsetWeight(weights[..items2], subset)
  decreases subset
{
  if subset == {} {
  } else {
    var x := SetMin(subset);
    assert x < items;
    assert weights[..items][x] == weights[x] == weights[..items2][x];
    SliceExtendWeight(weights, items, items2, subset - {x});
  }
}

lemma SliceExtendValue(values: seq<nat>, items: nat, items2: nat, subset: set<nat>)
  requires items <= items2 <= |values|
  requires forall i :: i in subset ==> i < items
  ensures SubsetValue(values[..items], subset) == SubsetValue(values[..items2], subset)
  decreases subset
{
  if subset == {} {
  } else {
    var x := SetMin(subset);
    assert x < items;
    assert values[..items][x] == values[x] == values[..items2][x];
    SliceExtendValue(values, items, items2, subset - {x});
  }
}

// =====================================================================
// Part 1: existence of a witness subset achieving OptVal
// =====================================================================
lemma OptValFeasible(weights: seq<nat>, values: seq<nat>, i: nat, w: nat)
  requires i <= |weights| && i <= |values| && |weights| == |values|
  ensures exists subset: set<nat> ::
    ValidSubset(i, subset) &&
    SubsetWeight(weights[..i], subset) <= w &&
    SubsetValue(values[..i], subset) == OptVal(weights, values, i, w)
  decreases i
{
  if i == 0 {
    assert ValidSubset(0, {});
    assert SubsetWeight(weights[..0], {}) == 0;
    assert SubsetValue(values[..0], {}) == 0;
  } else if weights[i-1] <= w {
    var excl := OptVal(weights, values, i-1, w);
    var incl := OptVal(weights, values, i-1, w - weights[i-1]) + values[i-1];
    if excl >= incl {
      // We exclude item i-1
      OptValFeasible(weights, values, i-1, w);
      var s: set<nat> :| ValidSubset(i-1, s) &&
        SubsetWeight(weights[..i-1], s) <= w &&
        SubsetValue(values[..i-1], s) == excl;
      assert ValidSubset(i, s);
      SliceExtendWeight(weights, i-1, i, s);
      SliceExtendValue(values, i-1, i, s);
    } else {
      // We include item i-1
      OptValFeasible(weights, values, i-1, w - weights[i-1]);
      var s: set<nat> :| ValidSubset(i-1, s) &&
        SubsetWeight(weights[..i-1], s) <= w - weights[i-1] &&
        SubsetValue(values[..i-1], s) == OptVal(weights, values, i-1, w - weights[i-1]);
      assert i - 1 !in s; // all elements of s are < i-1
      var ns := s + {i-1};
      assert ValidSubset(i, ns);

      // Show weight
      SubsetWeightRemove(weights[..i], ns, i-1);
      assert weights[..i][i-1] == weights[i-1];
      assert ns - {i-1} == s;
      SliceExtendWeight(weights, i-1, i, s);

      // Show value
      SubsetValueRemove(values[..i], ns, i-1);
      assert values[..i][i-1] == values[i-1];
      SliceExtendValue(values, i-1, i, s);
    }
  } else {
    // Item i-1 too heavy, must exclude
    OptValFeasible(weights, values, i-1, w);
    var s: set<nat> :| ValidSubset(i-1, s) &&
      SubsetWeight(weights[..i-1], s) <= w &&
      SubsetValue(values[..i-1], s) == OptVal(weights, values, i-1, w);
    assert ValidSubset(i, s);
    SliceExtendWeight(weights, i-1, i, s);
    SliceExtendValue(values, i-1, i, s);
  }
}

// =====================================================================
// Part 2: no subset of 0..i-1 with weight <= w has value > OptVal(i, w)
// =====================================================================
lemma OptValOptimal(weights: seq<nat>, values: seq<nat>, i: nat, w: nat, subset: set<nat>)
  requires i <= |weights| && i <= |values| && |weights| == |values|
  requires ValidSubset(i, subset)
  requires SubsetWeight(weights[..i], subset) <= w
  ensures SubsetValue(values[..i], subset) <= OptVal(weights, values, i, w)
  decreases i
{
  if i == 0 {
    assert subset == {};
  } else {
    if i - 1 in subset {
      // Subset includes item i-1
      var rest := subset - {i-1};
      assert ValidSubset(i-1, rest);
      SubsetWeightRemove(weights[..i], subset, i-1);
      assert weights[..i][i-1] == weights[i-1];
      SliceExtendWeight(weights, i-1, i, rest);
      SubsetValueRemove(values[..i], subset, i-1);
      assert values[..i][i-1] == values[i-1];
      SliceExtendValue(values, i-1, i, rest);
      OptValOptimal(weights, values, i-1, w - weights[i-1], rest);
    } else {
      // Subset excludes item i-1
      assert ValidSubset(i-1, subset);
      SliceExtendWeight(weights, i-1, i, subset);
      SliceExtendValue(values, i-1, i, subset);
      OptValOptimal(weights, values, i-1, w, subset);
    }
  }
}

// =====================================================================
// Connecting OptVal to IsOptimalValue
// =====================================================================
lemma OptValImpliesIsOptimalValue(weights: seq<nat>, values: seq<nat>, capacity: nat, items: nat)
  requires items <= |weights| && items <= |values| && |weights| == |values|
  ensures IsOptimalValue(weights, values, capacity, items, OptVal(weights, values, items, capacity))
{
  OptValFeasible(weights, values, items, capacity);
  var wit: set<nat> :| ValidSubset(items, wit) &&
    SubsetWeight(weights[..items], wit) <= capacity &&
    SubsetValue(values[..items], wit) == OptVal(weights, values, items, capacity);
  assert FeasibleSubset(weights, capacity, items, wit);
  forall subset: set<nat> | ValidSubset(items, subset) && FeasibleSubset(weights, capacity, items, subset)
    ensures SubsetValue(values[..items], subset) <= OptVal(weights, values, items, capacity)
  {
    assert SubsetWeight(weights[..items], subset) <= capacity;
    OptValOptimal(weights, values, items, capacity, subset);
  }
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
    invariant 0 <= w <= W + 1
    invariant forall ww :: 0 <= ww < w ==> dp[0, ww] == 0
  {
    dp[0, w] := 0;
    w := w + 1;
  }

  assert forall ww :: 0 <= ww <= W ==> dp[0, ww] == OptVal(weights, values, 0, ww);

  // Fill DP table
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant forall ii, ww :: 0 <= ii < i && 0 <= ww <= W ==>
      dp[ii, ww] == OptVal(weights, values, ii, ww)
  {
    w := 0;
    while w <= W
      invariant 0 <= w <= W + 1
      invariant forall ii, ww :: 0 <= ii < i && 0 <= ww <= W ==>
        dp[ii, ww] == OptVal(weights, values, ii, ww)
      invariant forall ww :: 0 <= ww < w ==>
        dp[i, ww] == OptVal(weights, values, i, ww)
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
  assert maxVal == OptVal(weights, values, n, W);
  OptValImpliesIsOptimalValue(weights, values, W, n);
}
