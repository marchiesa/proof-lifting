// 0/1 Knapsack -- Test cases

function SumValues(values: seq<int>): int
{
  if |values| == 0 then 0
  else values[0] + SumValues(values[1..])
}

method {:axiom} Knapsack(weights: seq<int>, values: seq<int>, W: int) returns (maxVal: int)
  requires |weights| == |values|
  requires W >= 0
  requires forall i :: 0 <= i < |weights| ==> weights[i] > 0
  requires forall i :: 0 <= i < |values| ==> values[i] >= 0
  ensures maxVal >= 0
  ensures maxVal <= SumValues(values)

method TestBasic()
{
  var weights := [1, 2, 3];
  var values := [6, 10, 12];
  var result := Knapsack(weights, values, 5);
  assert result >= 0;
}

method TestZeroCapacity()
{
  var weights := [1];
  var values := [10];
  var result := Knapsack(weights, values, 0);
  assert result >= 0;
  assert result <= SumValues(values);
}

method TestEmpty()
{
  var weights: seq<int> := [];
  var values: seq<int> := [];
  var result := Knapsack(weights, values, 10);
  assert result >= 0;
  assert result <= 0;
  assert result == 0;
}

method TestSingleFits()
{
  var weights := [3];
  var values := [5];
  var result := Knapsack(weights, values, 5);
  assert result >= 0;
  assert result <= SumValues(values);
}
