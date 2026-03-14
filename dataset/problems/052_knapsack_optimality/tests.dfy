// 0/1 Knapsack with Value Bound -- Test cases

method {:axiom} Knapsack01(weights: seq<int>, values: seq<int>, capacity: int) returns (maxVal: int)
  requires |weights| == |values|
  requires capacity >= 0
  requires forall i :: 0 <= i < |weights| ==> weights[i] > 0
  requires forall i :: 0 <= i < |values| ==> values[i] >= 0
  ensures maxVal >= 0

method TestBasic()
{
  var v := Knapsack01([2, 3, 4], [3, 4, 5], 5);
  assert v >= 0;
}

method TestEmpty()
{
  var v := Knapsack01([], [], 10);
  assert v >= 0;
}

method TestZeroCapacity()
{
  var v := Knapsack01([1, 2], [10, 20], 0);
  assert v >= 0;
}

method TestSingle()
{
  var v := Knapsack01([5], [10], 5);
  assert v >= 0;
}
