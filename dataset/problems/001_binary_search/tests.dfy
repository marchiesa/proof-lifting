// Binary Search -- Runtime spec tests

predicate IsSorted(a: seq<int>)
{
  forall i, j | 0 <= i < j < |a| :: a[i] <= a[j]
}

method Main()
{
  // Test IsSorted predicate
  expect IsSorted([1, 2, 3, 4, 5]), "ascending sequence should be sorted";
  expect IsSorted([1, 1, 2, 2, 3]), "sequence with duplicates should be sorted";
  expect IsSorted([42]), "single element should be sorted";
  expect IsSorted([]), "empty sequence should be sorted";
  expect !IsSorted([3, 1, 2]), "unsorted sequence should not be sorted";
  expect !IsSorted([1, 3, 2]), "[1,3,2] should not be sorted";
  expect !IsSorted([5, 4, 3, 2, 1]), "descending should not be sorted";
  expect IsSorted([1, 1, 1, 1]), "all equal should be sorted";
  expect IsSorted([-3, -1, 0, 2, 5]), "sequence with negatives should be sorted";
  expect !IsSorted([1, 2, 3, 2]), "last element out of order should not be sorted";

  print "All spec tests passed\n";
}
