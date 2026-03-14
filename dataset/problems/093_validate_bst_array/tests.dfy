// Validate BST Property on Array -- Runtime spec tests

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

// Bounded version for runtime checking
function IsSortedBounded(a: seq<int>): bool
{
  if |a| <= 1 then true
  else a[0] < a[1] && IsSortedBounded(a[1..])
}

method Main()
{
  // Positive: sorted arrays satisfy IsSorted
  expect IsSortedBounded([1, 2, 3, 4, 5]), "Sorted array should satisfy IsSorted";
  expect IsSortedBounded([]), "Empty array should satisfy IsSorted";
  expect IsSortedBounded([42]), "Single element should satisfy IsSorted";
  expect IsSortedBounded([-3, -1, 0, 5, 10]), "Sorted with negatives should satisfy IsSorted";

  // Negative: unsorted arrays should not satisfy IsSorted
  expect !IsSortedBounded([1, 3, 2, 4, 5]), "Unsorted array should not satisfy IsSorted";
  expect !IsSortedBounded([5, 4, 3, 2, 1]), "Reverse sorted should not satisfy IsSorted";
  expect !IsSortedBounded([1, 1, 2]), "Duplicates should not satisfy strict IsSorted";
  expect !IsSortedBounded([2, 1]), "Decreasing pair should not satisfy IsSorted";

  // Edge cases
  expect IsSortedBounded([1, 2]), "Two element sorted should pass";
  expect !IsSortedBounded([2, 2]), "Equal pair should not satisfy strict sort";

  print "All spec tests passed\n";
}
