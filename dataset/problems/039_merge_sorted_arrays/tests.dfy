// Merge Two Sorted Arrays -- Runtime spec tests

predicate IsSorted(a: seq<int>)
{
  forall i, j | 0 <= i < j < |a| :: a[i] <= a[j]
}

method Main() {
  // IsSorted positive
  expect IsSorted([]), "empty sorted";
  expect IsSorted([1]), "singleton sorted";
  expect IsSorted([1, 2, 3, 4, 5]), "ascending sorted";
  expect IsSorted([1, 1, 2, 2, 3]), "non-decreasing sorted";
  expect IsSorted([5, 5, 5]), "all equal sorted";

  // IsSorted negative
  expect !IsSorted([2, 1]), "descending not sorted";
  expect !IsSorted([1, 3, 2]), "out of order not sorted";
  expect !IsSorted([5, 4, 3, 2, 1]), "reversed not sorted";

  // Test multiset merging property manually
  var a: seq<int> := [1, 3, 5];
  var b: seq<int> := [2, 4, 6];
  var merged: seq<int> := [1, 2, 3, 4, 5, 6];
  expect IsSorted(merged), "merged result should be sorted";
  expect multiset(merged) == multiset(a) + multiset(b), "merged multiset equals sum";

  // Another merge scenario
  var c: seq<int> := [1, 2, 2];
  var d: seq<int> := [2, 3, 3];
  var merged2: seq<int> := [1, 2, 2, 2, 3, 3];
  expect IsSorted(merged2), "merged with dups should be sorted";
  expect multiset(merged2) == multiset(c) + multiset(d), "multiset preserved with dups";

  print "All spec tests passed\n";
}
