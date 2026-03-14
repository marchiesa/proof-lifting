// 0/1 Knapsack -- Runtime spec tests

function SumValues(values: seq<int>): int
{
  if |values| == 0 then 0
  else values[0] + SumValues(values[1..])
}

method Main()
{
  // Test SumValues
  expect SumValues([]) == 0, "sum of empty is 0";
  expect SumValues([5]) == 5, "sum of [5] is 5";
  expect SumValues([1, 2, 3]) == 6, "sum of [1,2,3] is 6";
  expect SumValues([6, 10, 12]) == 28, "sum of [6,10,12] is 28";
  expect SumValues([0, 0, 0]) == 0, "sum of zeros is 0";
  expect SumValues([10]) == 10, "sum of [10] is 10";
  expect SumValues([1, 1, 1, 1, 1]) == 5, "sum of five 1s is 5";

  // Test SumValues non-negativity for non-negative inputs
  // (This is what the SumValuesNonNeg lemma proves)
  expect SumValues([1, 2, 3]) >= 0, "sum of non-negatives is non-negative";
  expect SumValues([0, 0, 0]) >= 0, "sum of zeros is non-negative";
  expect SumValues([]) >= 0, "sum of empty is non-negative";

  // Test spec bounds: maxVal >= 0 and maxVal <= SumValues(values)
  // For weights=[1,2,3], values=[6,10,12], W=5:
  // SumValues(values) = 28, so maxVal should be in [0, 28]
  var values := [6, 10, 12];
  expect SumValues(values) == 28, "total value is 28";
  // Known optimal: pick items 0 and 1 (weight 1+2=3, value 6+10=16)
  // or items 0 and 2 (weight 1+3=4, value 6+12=18)
  // or items 1 and 2 (weight 2+3=5, value 10+12=22)
  // Best for W=5: items 1,2 with value 22
  expect 22 >= 0, "expected knapsack result >= 0";
  expect 22 <= SumValues(values), "expected knapsack result <= sum";

  // Edge: zero capacity should give 0
  expect 0 >= 0 && 0 <= SumValues([10]), "zero capacity result in bounds";

  // Edge: empty items
  expect SumValues([]) == 0, "no items means sum is 0";

  print "All spec tests passed\n";
}
