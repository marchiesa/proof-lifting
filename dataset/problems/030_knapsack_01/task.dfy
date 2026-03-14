// 0/1 Knapsack
// Task: Add loop invariants so that Dafny can verify this program.

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
  {
    var j := W;
    while j >= weights[i]
    {
      if dp[j - weights[i]] + values[i] > dp[j] {
        dp := dp[j := dp[j - weights[i]] + values[i]];
      }
      j := j - 1;
    }
    i := i + 1;
  }

  maxVal := dp[W];
}
