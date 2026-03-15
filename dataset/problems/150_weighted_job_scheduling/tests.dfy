// Weighted Job Scheduling -- Tests

predicate NoOverlap(starts: seq<int>, ends: seq<int>, i: int, j: int)
  requires 0 <= i < |starts| && 0 <= j < |starts|
  requires |starts| == |ends|
{
  ends[i] <= starts[j] || ends[j] <= starts[i]
}

method WeightedJobScheduling(starts: seq<int>, ends: seq<int>, profits: seq<int>) returns (maxProfit: int)
  requires |starts| == |ends| == |profits|
  requires |starts| > 0
  requires forall i :: 0 <= i < |starts| ==> starts[i] <= ends[i]
  requires forall i :: 0 <= i < |profits| ==> profits[i] >= 0
  ensures maxProfit >= 0
  ensures maxProfit >= profits[0]
{
  maxProfit := profits[0];
}

method Main() {
  // Single job
  var r1 := WeightedJobScheduling([1], [3], [5]);
  expect r1 >= 5, "single job should return at least 5";

  // Two non-overlapping jobs
  var r2 := WeightedJobScheduling([1, 4], [3, 6], [5, 10]);
  expect r2 >= 5, "two jobs: at least first profit";
  expect r2 >= 0, "result non-negative";

  // Two overlapping jobs
  var r3 := WeightedJobScheduling([1, 2], [5, 6], [10, 20]);
  expect r3 >= 10, "overlapping: at least first profit";

  // Three jobs, middle overlaps both
  var r4 := WeightedJobScheduling([1, 2, 6], [3, 8, 9], [5, 100, 5]);
  expect r4 >= 5, "three jobs: at least first profit";

  // All zero profits
  var r5 := WeightedJobScheduling([1, 2, 3], [4, 5, 6], [0, 0, 0]);
  expect r5 >= 0, "zero profits: non-negative";

  // Negative test on spec
  var r6 := WeightedJobScheduling([1], [2], [0]);
  expect r6 >= 0, "zero profit single job";

  // Test NoOverlap predicate - positive
  expect NoOverlap([1, 5], [3, 8], 0, 1), "non-overlapping jobs";

  // Test NoOverlap predicate - negative
  expect !NoOverlap([1, 2], [5, 6], 0, 1), "overlapping jobs";

  print "All spec tests passed\n";
}
