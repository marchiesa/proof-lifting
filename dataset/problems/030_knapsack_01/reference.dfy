// 0/1 Knapsack -- Reference solution with invariants

function SumValues(values: seq<int>): int
{
  if |values| == 0 then 0
  else values[0] + SumValues(values[1..])
}

lemma SumValuesNonNeg(values: seq<int>)
  requires forall i :: 0 <= i < |values| ==> values[i] >= 0
  ensures SumValues(values) >= 0
{
  if |values| > 0 {
    SumValuesNonNeg(values[1..]);
  }
}

lemma SumValuesMonotone(values: seq<int>, k: int)
  requires 0 <= k <= |values|
  requires forall i :: 0 <= i < |values| ==> values[i] >= 0
  ensures SumValues(values[..k]) <= SumValues(values)
{
  if k < |values| {
    SumValuesNonNeg(values[..k]);
    assert values == values[..k] + values[k..];
    SumValuesSplit(values[..k], values[k..]);
    SumValuesNonNeg(values[k..]);
  } else {
    assert values[..k] == values;
  }
}

lemma SumValuesSplit(a: seq<int>, b: seq<int>)
  ensures SumValues(a + b) == SumValues(a) + SumValues(b)
{
  if |a| == 0 {
    assert a + b == b;
  } else {
    assert (a + b)[0] == a[0];
    assert (a + b)[1..] == a[1..] + b;
    SumValuesSplit(a[1..], b);
  }
}

method Knapsack(weights: seq<int>, values: seq<int>, W: int) returns (maxVal: int)
  requires |weights| == |values|
  requires W >= 0
  requires forall i :: 0 <= i < |weights| ==> weights[i] > 0
  requires forall i :: 0 <= i < |values| ==> values[i] >= 0
  ensures maxVal >= 0
  ensures maxVal <= SumValues(values)
{
  var n := |weights|;
  SumValuesNonNeg(values);

  if n == 0 {
    return 0;
  }

  // dp[j] = max value achievable with capacity j using items considered so far
  var dp := seq(W + 1, _ => 0);

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |dp| == W + 1
    invariant forall j :: 0 <= j <= W ==> dp[j] >= 0
    invariant forall j :: 0 <= j <= W ==> dp[j] <= SumValues(values[..i])
    decreases n - i
  {
    var j := W;
    while j >= weights[i]
      invariant -1 <= j <= W
      invariant |dp| == W + 1
      invariant forall k :: 0 <= k <= W ==> dp[k] >= 0
      invariant forall k :: 0 <= k <= j ==> dp[k] <= SumValues(values[..i])
      invariant forall k :: j < k <= W ==> dp[k] <= SumValues(values[..i]) + values[i]
      decreases j
    {
      if dp[j - weights[i]] + values[i] > dp[j] {
        assert dp[j - weights[i]] <= SumValues(values[..i]);
        dp := dp[j := dp[j - weights[i]] + values[i]];
      }
      j := j - 1;
    }
    assert forall k :: 0 <= k <= W ==> dp[k] <= SumValues(values[..i]) + values[i];
    assert values[..i + 1] == values[..i] + [values[i]];
    SumValuesSplit(values[..i], [values[i]]);
    assert SumValues(values[..i + 1]) == SumValues(values[..i]) + values[i];
    i := i + 1;
  }

  assert values[..n] == values;
  maxVal := dp[W];
}
