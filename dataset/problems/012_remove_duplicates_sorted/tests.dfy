// Remove Duplicates from Sorted Sequence -- Runtime spec tests

predicate IsSorted(a: seq<int>)
{
  forall i, j | 0 <= i < j < |a| :: a[i] <= a[j]
}

predicate IsStrictlySorted(a: seq<int>)
{
  forall i, j | 0 <= i < j < |a| :: a[i] < a[j]
}

method Main()
{
  // Test IsSorted
  expect IsSorted([1, 1, 2, 3, 3, 3, 4]), "sorted with duplicates";
  expect IsSorted([1, 2, 3]), "strictly sorted is also sorted";
  expect IsSorted([]), "empty is sorted";
  expect !IsSorted([3, 1, 2]), "unsorted is not sorted";

  // Test IsStrictlySorted - positive cases
  expect IsStrictlySorted([1, 2, 3, 4]), "strictly increasing";
  expect IsStrictlySorted([]), "empty is strictly sorted";
  expect IsStrictlySorted([42]), "single element is strictly sorted";
  expect IsStrictlySorted([-3, 0, 5, 10]), "increasing with gaps";

  // Test IsStrictlySorted - negative cases
  expect !IsStrictlySorted([1, 1, 2]), "duplicates break strict sorting";
  expect !IsStrictlySorted([1, 2, 2, 3]), "interior duplicate breaks it";
  expect !IsStrictlySorted([3, 2, 1]), "descending is not strictly sorted";
  expect !IsStrictlySorted([1, 1]), "two equal elements not strictly sorted";

  // Verify that strictly sorted implies sorted
  expect IsSorted([1, 2, 3, 4]) && IsStrictlySorted([1, 2, 3, 4]),
    "strictly sorted implies sorted";

  // Verify that sorted does not imply strictly sorted
  expect IsSorted([1, 1, 2]) && !IsStrictlySorted([1, 1, 2]),
    "sorted but not strictly sorted";

  print "All spec tests passed\n";
}
