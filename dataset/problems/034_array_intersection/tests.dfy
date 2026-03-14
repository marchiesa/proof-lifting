// Array Intersection of Two Sorted Arrays -- Runtime spec tests

predicate IsSorted(a: seq<int>)
{
  forall i, j | 0 <= i < j < |a| :: a[i] <= a[j]
}

predicate StrictlySorted(a: seq<int>)
{
  forall i, j | 0 <= i < j < |a| :: a[i] < a[j]
}

predicate IsSubsetOf(a: seq<int>, b: seq<int>)
{
  forall x | x in a :: x in b
}

method Main() {
  // IsSorted positive
  expect IsSorted([1, 2, 3, 4]), "ascending is sorted";
  expect IsSorted([1, 1, 2, 3]), "non-decreasing is sorted";
  expect IsSorted([]), "empty is sorted";
  expect IsSorted([5]), "singleton is sorted";

  // IsSorted negative
  expect !IsSorted([3, 1, 2]), "unsorted is not sorted";
  expect !IsSorted([2, 1]), "descending pair not sorted";

  // StrictlySorted positive
  expect StrictlySorted([1, 2, 3, 4]), "ascending is strictly sorted";
  expect StrictlySorted([]), "empty is strictly sorted";
  expect StrictlySorted([5]), "singleton is strictly sorted";

  // StrictlySorted negative
  expect !StrictlySorted([1, 1, 2, 3]), "duplicates not strictly sorted";
  expect !StrictlySorted([3, 1]), "descending not strictly sorted";
  expect !StrictlySorted([1, 2, 2, 3]), "adjacent dups not strictly sorted";

  // IsSubsetOf positive
  expect IsSubsetOf([1, 3], [1, 2, 3, 4]), "[1,3] subset of [1,2,3,4]";
  expect IsSubsetOf([], [1, 2, 3]), "empty is subset of anything";
  expect IsSubsetOf([1, 2], [1, 2]), "same seq is subset";
  expect IsSubsetOf([], []), "empty subset of empty";

  // IsSubsetOf negative
  expect !IsSubsetOf([1, 5], [1, 2, 3]), "[1,5] not subset of [1,2,3]";
  expect !IsSubsetOf([10], [1, 2, 3]), "[10] not subset of [1,2,3]";

  print "All spec tests passed\n";
}
