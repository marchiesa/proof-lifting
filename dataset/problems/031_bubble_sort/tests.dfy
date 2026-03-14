// Bubble Sort -- Runtime spec tests

predicate IsSorted(a: seq<int>)
{
  forall i, j | 0 <= i < j < |a| :: a[i] <= a[j]
}

method Main() {
  // Positive cases: sorted sequences
  expect IsSorted([]), "empty should be sorted";
  expect IsSorted([1]), "singleton should be sorted";
  expect IsSorted([1, 2, 3, 4, 5]), "ascending should be sorted";
  expect IsSorted([1, 1, 1]), "all equal should be sorted";
  expect IsSorted([1, 1, 2, 3, 3]), "non-decreasing should be sorted";

  // Negative cases: unsorted sequences
  expect !IsSorted([2, 1]), "descending pair should not be sorted";
  expect !IsSorted([3, 1, 2]), "unsorted should not be sorted";
  expect !IsSorted([1, 3, 2, 4]), "one swap should not be sorted";
  expect !IsSorted([5, 4, 3, 2, 1]), "reversed should not be sorted";

  print "All spec tests passed\n";
}
