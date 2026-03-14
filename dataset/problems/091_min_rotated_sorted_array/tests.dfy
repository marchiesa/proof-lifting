// Find Minimum in Rotated Sorted Array -- Runtime spec tests

function SeqMin(a: seq<int>): int
  requires |a| > 0
  decreases |a|
{
  if |a| == 1 then a[0]
  else if a[0] <= SeqMin(a[1..]) then a[0]
  else SeqMin(a[1..])
}

method Main()
{
  // Positive: SeqMin of single element
  expect SeqMin([42]) == 42, "SeqMin of [42] should be 42";

  // Positive: SeqMin of sorted array
  expect SeqMin([1, 2, 3, 4, 5]) == 1, "SeqMin of sorted array should be 1";

  // Positive: SeqMin of rotated sorted array
  expect SeqMin([3, 4, 5, 1, 2]) == 1, "SeqMin of rotated [3,4,5,1,2] should be 1";

  // Positive: SeqMin of two elements
  expect SeqMin([2, 1]) == 1, "SeqMin of [2,1] should be 1";

  // Positive: SeqMin of reverse sorted
  expect SeqMin([5, 4, 3, 2, 1]) == 1, "SeqMin of [5,4,3,2,1] should be 1";

  // Positive: min is at beginning
  expect SeqMin([1, 5, 3, 7]) == 1, "SeqMin of [1,5,3,7] should be 1";

  // Positive: min is at end
  expect SeqMin([5, 3, 7, 1]) == 1, "SeqMin of [5,3,7,1] should be 1";

  // Negative: SeqMin should not equal non-min element
  expect SeqMin([3, 1, 2]) != 3, "SeqMin of [3,1,2] should not be 3";
  expect SeqMin([3, 1, 2]) != 2, "SeqMin of [3,1,2] should not be 2";

  // Positive: all same elements
  expect SeqMin([5, 5, 5]) == 5, "SeqMin of [5,5,5] should be 5";

  // Negative values
  expect SeqMin([-3, -1, -2]) == -3, "SeqMin of [-3,-1,-2] should be -3";

  print "All spec tests passed\n";
}
