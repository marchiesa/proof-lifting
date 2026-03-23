// Pattern: Compute weighted average (sum of weights * values / sum of weights)
// Source: ML libraries (weighted loss), statistics, grading systems
// Real-world: GPA calculation, portfolio returns, sensor fusion

ghost function WeightedSum(values: seq<int>, weights: seq<int>): int
  requires |values| == |weights|
{
  if |values| == 0 then 0
  else WeightedSum(values[..|values|-1], weights[..|weights|-1])
       + values[|values|-1] * weights[|weights|-1]
}

ghost function SumSeq(s: seq<int>): int
{
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

method ComputeWeightedSum(values: seq<int>, weights: seq<int>) returns (wsum: int, wcount: int)
  requires |values| == |weights|
  ensures wsum == WeightedSum(values, weights)
  ensures wcount == SumSeq(weights)
{
  wsum := 0;
  wcount := 0;
  var i := 0;
  while i < |values|
    invariant 0 <= i <= |values|
    invariant wsum == WeightedSum(values[..i], weights[..i])
    invariant wcount == SumSeq(weights[..i])
  {
    assert values[..i+1] == values[..i] + [values[i]];      // SMT QUIRK: B1 extensionality
    assert weights[..i+1] == weights[..i] + [weights[i]];    // SMT QUIRK: B1 extensionality
    wsum := wsum + values[i] * weights[i];
    wcount := wcount + weights[i];
    i := i + 1;
  }
  assert values[..|values|] == values;    // SMT QUIRK: B1 take-full
  assert weights[..|weights|] == weights;  // SMT QUIRK: B1 take-full
}
