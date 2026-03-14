// Median of Two Sorted Arrays -- Runtime spec tests

function MergeSpec(a: seq<int>, b: seq<int>): seq<int>
{
  if |a| == 0 then b
  else if |b| == 0 then a
  else if a[0] <= b[0] then [a[0]] + MergeSpec(a[1..], b)
  else [b[0]] + MergeSpec(a, b[1..])
}

// Bounded IsSorted for runtime
function IsSortedBounded(a: seq<int>): bool
{
  if |a| <= 1 then true
  else a[0] <= a[1] && IsSortedBounded(a[1..])
}

method Main()
{
  // MergeSpec: basic merges
  expect MergeSpec([1, 3], [2]) == [1, 2, 3], "Merge [1,3] and [2] = [1,2,3]";
  expect MergeSpec([1, 3, 5], [2, 4, 6]) == [1, 2, 3, 4, 5, 6],
    "Merge [1,3,5] and [2,4,6] = [1,2,3,4,5,6]";

  // MergeSpec: empty arrays
  expect MergeSpec([], [1, 2, 3]) == [1, 2, 3], "Merge [] and [1,2,3]";
  expect MergeSpec([1, 2, 3], []) == [1, 2, 3], "Merge [1,2,3] and []";
  var empty: seq<int> := [];
  expect MergeSpec(empty, empty) == [], "Merge [] and []";

  // MergeSpec: duplicates
  expect MergeSpec([1, 2, 2], [2, 3]) == [1, 2, 2, 2, 3], "Merge with duplicates";

  // MergeSpec: length preservation
  expect |MergeSpec([1, 3], [2, 4])| == 4, "Merge length = sum of lengths";

  // MergeSpec: result is sorted
  expect IsSortedBounded(MergeSpec([1, 3, 5], [2, 4, 6])), "Merge result is sorted";
  expect IsSortedBounded(MergeSpec([1], [2])), "Merge [1] and [2] is sorted";

  // MergeSpec: negative test
  expect MergeSpec([1, 3], [2]) != [1, 3, 2], "Merge should interleave properly";
  expect MergeSpec([1, 3], [2]) != [2, 1, 3], "Merge should start with smallest";

  // MergeSpec: single elements
  expect MergeSpec([1], [2]) == [1, 2], "Merge [1] and [2] = [1,2]";
  expect MergeSpec([2], [1]) == [1, 2], "Merge [2] and [1] = [1,2]";

  // IsSortedBounded tests
  expect IsSortedBounded([1, 2, 3]), "[1,2,3] is sorted";
  expect IsSortedBounded([1, 1, 2]), "[1,1,2] is sorted (non-strict)";
  expect !IsSortedBounded([2, 1]), "[2,1] is not sorted";

  print "All spec tests passed\n";
}
