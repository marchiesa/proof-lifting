// Is Sorted Check -- Runtime spec tests

predicate IsSorted(a: seq<int>)
{
  forall i, j | 0 <= i < j < |a| :: a[i] <= a[j]
}

method Main()
{
  // Positive cases - should be sorted
  expect IsSorted([1, 2, 3, 4, 5]), "ascending should be sorted";
  expect IsSorted([5, 5, 5, 5]), "all equal should be sorted";
  expect IsSorted([]), "empty should be sorted";
  expect IsSorted([42]), "single element should be sorted";
  expect IsSorted([1, 1, 2, 2, 3, 3]), "non-decreasing with dupes should be sorted";
  expect IsSorted([-5, -3, 0, 1, 10]), "negatives to positives should be sorted";

  // Negative cases - should not be sorted
  expect !IsSorted([5, 4, 3, 2, 1]), "descending should not be sorted";
  expect !IsSorted([1, 3, 2, 4]), "one inversion should not be sorted";
  expect !IsSorted([2, 1]), "simple swap should not be sorted";
  expect !IsSorted([1, 2, 3, 2]), "last element out of order should not be sorted";
  expect !IsSorted([3, 1, 2]), "3,1,2 should not be sorted";

  print "All spec tests passed\n";
}
