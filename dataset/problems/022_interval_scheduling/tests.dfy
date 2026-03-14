// Interval Scheduling (Greedy) -- Runtime spec tests

predicate SortedByEnd(ends: seq<int>)
{
  forall i, j | 0 <= i < j < |ends| :: ends[i] <= ends[j]
}

method Main()
{
  // Test SortedByEnd
  expect SortedByEnd([2, 4, 6, 7, 9, 9]), "sorted end times";
  expect SortedByEnd([1, 1, 1]), "all equal end times";
  expect SortedByEnd([]), "empty is sorted";
  expect SortedByEnd([5]), "single element";
  expect !SortedByEnd([5, 3, 7]), "unsorted end times";
  expect !SortedByEnd([2, 1]), "2,1 not sorted";
  expect SortedByEnd([1, 2, 3, 4, 5]), "strictly increasing";

  // Test the non-overlapping property concept:
  // selected intervals are non-overlapping if end[i] <= start[j] for i < j
  var starts := [1, 3, 0, 5, 8, 5];
  var ends := [2, 4, 6, 7, 9, 9];
  // A valid schedule might be indices [0, 1, 3, 4]: intervals (1,2), (3,4), (5,7), (8,9)
  // Check: end[0]=2 <= start[1]=3, end[1]=4 <= start[3]=5, end[3]=7 <= start[4]=8
  expect ends[0] <= starts[1], "interval 0 ends before interval 1 starts";
  expect ends[1] <= starts[3], "interval 1 ends before interval 3 starts";
  expect ends[3] <= starts[4], "interval 3 ends before interval 4 starts";

  // Invalid schedule: overlapping intervals
  // intervals 0 and 2: (1,2) and (0,6) overlap since end[0]=2 > start[2]=0
  // but we check end[0] <= start[2]: 2 <= 0 is false
  expect !(ends[0] <= starts[2]), "intervals 0 and 2 overlap";

  // Test precondition: start < end for each interval
  expect starts[0] < ends[0], "interval 0: start < end";
  expect starts[1] < ends[1], "interval 1: start < end";
  expect starts[2] < ends[2], "interval 2: start < end";

  print "All spec tests passed\n";
}
