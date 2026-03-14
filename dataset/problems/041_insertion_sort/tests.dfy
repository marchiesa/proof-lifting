// Insertion Sort -- Runtime spec tests

predicate IsSorted(a: seq<int>)
{
  forall i, j | 0 <= i < j < |a| :: a[i] <= a[j]
}

method Main() {
  // IsSorted positive
  expect IsSorted([]), "empty sorted";
  expect IsSorted([42]), "singleton sorted";
  expect IsSorted([1, 2, 3, 4, 5]), "ascending sorted";
  expect IsSorted([1, 1, 2, 3, 3]), "non-decreasing sorted";
  expect IsSorted([7, 7, 7]), "all equal sorted";

  // IsSorted negative
  expect !IsSorted([5, 3, 1, 4, 2]), "random order not sorted";
  expect !IsSorted([4, 3, 2, 1]), "reversed not sorted";
  expect !IsSorted([1, 3, 2]), "single swap not sorted";

  // Multiset preservation property
  var before := [5, 3, 1, 4, 2];
  var after := [1, 2, 3, 4, 5];
  expect IsSorted(after), "sorted version is sorted";
  expect multiset(before) == multiset(after), "multiset preserved after sorting";

  print "All spec tests passed\n";
}
