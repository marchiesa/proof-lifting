// Tests for Problem 1: 0/1 Knapsack with Optimality
include "task.dfy"

method Main()
{
  // Test 1: Simple example
  // Items: (weight=2, value=3), (weight=3, value=4), (weight=4, value=5)
  // Capacity: 5
  // Optimal: items 0 and 1 (weight=5, value=7)
  var weights := [2, 3, 4];
  var values := [3, 4, 5];
  var result := Knapsack(weights, values, 5);
  print "Test 1 - Knapsack([2,3,4], [3,4,5], cap=5): ", result, " (expected 7)\n";

  // Test 2: Single item fits
  var w2 := [5];
  var v2 := [10];
  var r2 := Knapsack(w2, v2, 5);
  print "Test 2 - Knapsack([5], [10], cap=5): ", r2, " (expected 10)\n";

  // Test 3: Single item doesn't fit
  var w3 := [6];
  var v3 := [10];
  var r3 := Knapsack(w3, v3, 5);
  print "Test 3 - Knapsack([6], [10], cap=5): ", r3, " (expected 0)\n";

  // Test 4: All items fit
  var w4 := [1, 2, 3];
  var v4 := [6, 10, 12];
  var r4 := Knapsack(w4, v4, 10);
  print "Test 4 - Knapsack([1,2,3], [6,10,12], cap=10): ", r4, " (expected 28)\n";

  // Test 5: Classic example
  // Items: (1,1), (3,4), (4,5), (5,7)
  // Capacity: 7
  // Optimal: items 1 and 2 (weight=7, value=9) or items 0,1,2 (weight=8 > 7)
  // Actually: items 1 and 3 (weight=8 > 7), items 0,1 (weight=4, value=5),
  //           items 0,3 (weight=6, value=8), items 2,3 (weight=9 > 7)
  //           items 0,2 (weight=5, value=6), items 1,2 (weight=7, value=9)
  var w5 := [1, 3, 4, 5];
  var v5 := [1, 4, 5, 7];
  var r5 := Knapsack(w5, v5, 7);
  print "Test 5 - Knapsack([1,3,4,5], [1,4,5,7], cap=7): ", r5, " (expected 9)\n";
}
