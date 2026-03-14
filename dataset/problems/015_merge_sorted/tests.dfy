// Merge Two Sorted Sequences -- Runtime spec tests

predicate IsSorted(a: seq<int>)
{
  forall i, j | 0 <= i < j < |a| :: a[i] <= a[j]
}

method Main()
{
  // Test IsSorted (the main spec predicate for merge result)
  expect IsSorted([1, 2, 3, 4, 5, 6]), "merged ascending is sorted";
  expect IsSorted([1, 1, 2, 2, 3, 3]), "merged with duplicates is sorted";
  expect IsSorted([]), "empty is sorted";
  expect IsSorted([42]), "single is sorted";
  expect !IsSorted([1, 3, 2, 4, 5, 6]), "unsorted merge result";

  // Test the inputs are sorted (precondition)
  expect IsSorted([1, 3, 5]), "first input sorted";
  expect IsSorted([2, 4, 6]), "second input sorted";

  // Verify multiset preservation concept:
  // multiset([1,2,3,4,5,6]) == multiset([1,3,5]) + multiset([2,4,6])
  expect multiset([1, 2, 3, 4, 5, 6]) == multiset([1, 3, 5]) + multiset([2, 4, 6]),
    "multiset of sorted merge equals sum of input multisets";

  // Edge cases
  expect multiset([1, 2]) == multiset([1, 2]) + multiset([]),
    "merging with empty preserves multiset";
  expect multiset([1, 1, 1, 1]) == multiset([1, 1]) + multiset([1, 1]),
    "merging duplicates preserves count";

  // Verify that sorted merge of sorted inputs should be sorted
  expect IsSorted([1, 2, 3]) && IsSorted([4, 5, 6]),
    "both inputs sorted";
  expect IsSorted([1, 2, 3, 4, 5, 6]), "expected merge result is sorted";

  print "All spec tests passed\n";
}
