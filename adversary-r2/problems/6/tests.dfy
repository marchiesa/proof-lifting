// Tests for Problem 6: Interval Scheduling Maximization
include "task.dfy"

method Main()
{
  // Test 1: Non-overlapping intervals
  // [1,3), [3,5), [5,7) => all 3 can be selected
  var intervals1 := [Interval(1, 3), Interval(3, 5), Interval(5, 7)];
  var c1, s1 := MaxNonOverlapping(intervals1);
  print "Test 1 - Non-overlapping [1,3),[3,5),[5,7): count=", c1, " (expected 3)\n";

  // Test 2: All overlapping
  // [1,10), [2,11), [3,12) => only 1
  var intervals2 := [Interval(1, 10), Interval(2, 11), Interval(3, 12)];
  var c2, s2 := MaxNonOverlapping(intervals2);
  print "Test 2 - All overlapping: count=", c2, " (expected 1)\n";

  // Test 3: Classic example
  // [1,4), [3,5), [0,6), [5,7), [3,9), [5,9), [6,10), [8,11), [8,12), [2,14), [12,16)
  // Greedy by end: [1,4), [5,7), [8,11), [12,16) => 4
  var intervals3 := [
    Interval(1, 4), Interval(3, 5), Interval(0, 6), Interval(5, 7),
    Interval(3, 9), Interval(5, 9), Interval(6, 10), Interval(8, 11),
    Interval(8, 12), Interval(2, 14), Interval(12, 16)
  ];
  var c3, s3 := MaxNonOverlapping(intervals3);
  print "Test 3 - Classic 11 intervals: count=", c3, " (expected 4)\n";

  // Test 4: Single interval
  var intervals4 := [Interval(0, 1)];
  var c4, s4 := MaxNonOverlapping(intervals4);
  print "Test 4 - Single interval: count=", c4, " (expected 1)\n";

  // Test 5: Two overlapping, pick the earlier-ending one
  // [1,5), [2,3) => pick [2,3), then [1,5) overlaps? No, [2,3) ends at 3, [1,5) starts at 1 < 3
  // So only [2,3). But wait: [1,5) and [2,3) overlap.
  // After sorting by end: [2,3), [1,5). Pick [2,3), skip [1,5). Count = 1.
  // But actually optimal is also 1, since they overlap.
  var intervals5 := [Interval(1, 5), Interval(2, 3)];
  var c5, s5 := MaxNonOverlapping(intervals5);
  print "Test 5 - Two overlapping: count=", c5, " (expected 1)\n";

  // Test 6: Nested intervals
  // [1,10), [2,3), [4,5), [6,7) => pick [2,3), [4,5), [6,7) = 3
  var intervals6 := [Interval(1, 10), Interval(2, 3), Interval(4, 5), Interval(6, 7)];
  var c6, s6 := MaxNonOverlapping(intervals6);
  print "Test 6 - Nested: count=", c6, " (expected 3)\n";
}
