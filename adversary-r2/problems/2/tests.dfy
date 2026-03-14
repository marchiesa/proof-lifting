// Tests for Problem 2: Longest Increasing Subsequence
include "task.dfy"

method Main()
{
  // Test 1: Classic example
  // [10, 9, 2, 5, 3, 7, 101, 18]
  // LIS: [2, 3, 7, 18] or [2, 5, 7, 18] or [2, 3, 7, 101] => length 4
  var a1 := [10, 9, 2, 5, 3, 7, 101, 18];
  var r1 := LIS(a1);
  print "Test 1 - LIS([10,9,2,5,3,7,101,18]): ", r1, " (expected 4)\n";

  // Test 2: Already sorted
  var a2 := [1, 2, 3, 4, 5];
  var r2 := LIS(a2);
  print "Test 2 - LIS([1,2,3,4,5]): ", r2, " (expected 5)\n";

  // Test 3: Reverse sorted
  var a3 := [5, 4, 3, 2, 1];
  var r3 := LIS(a3);
  print "Test 3 - LIS([5,4,3,2,1]): ", r3, " (expected 1)\n";

  // Test 4: Single element
  var a4 := [42];
  var r4 := LIS(a4);
  print "Test 4 - LIS([42]): ", r4, " (expected 1)\n";

  // Test 5: All same
  var a5 := [7, 7, 7, 7];
  var r5 := LIS(a5);
  print "Test 5 - LIS([7,7,7,7]): ", r5, " (expected 1)\n";

  // Test 6: Alternating
  var a6 := [1, 3, 2, 4, 3, 5];
  var r6 := LIS(a6);
  print "Test 6 - LIS([1,3,2,4,3,5]): ", r6, " (expected 4)\n";
}
