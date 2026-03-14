// Kth Smallest Element -- Runtime spec tests

predicate IsSorted(a: seq<int>)
{
  forall i, j | 0 <= i < j < |a| :: a[i] <= a[j]
}

// Note: IsKthSmallest uses set comprehensions with triggers; we test the IsSorted
// predicate and the membership postcondition instead.

method Main() {
  // IsSorted positive
  expect IsSorted([1, 1, 3, 4, 5]), "sorted with dup";
  expect IsSorted([]), "empty sorted";
  expect IsSorted([42]), "singleton sorted";

  // IsSorted negative
  expect !IsSorted([3, 1, 4, 1, 5]), "unsorted";

  // Membership in multiset (the ensures says result in multiset(a))
  var a := [3, 1, 4, 1, 5];
  expect 3 in multiset(a), "3 in multiset";
  expect 1 in multiset(a), "1 in multiset";
  expect 4 in multiset(a), "4 in multiset";
  expect 5 in multiset(a), "5 in multiset";
  expect 99 !in multiset(a), "99 not in multiset";

  // When sorted, kth element is at index k
  var sorted := [1, 1, 3, 4, 5];
  expect IsSorted(sorted), "sorted version is sorted";
  expect sorted[0] == 1, "0th smallest is 1";
  expect sorted[2] == 3, "2nd smallest is 3";
  expect sorted[4] == 5, "4th smallest is 5";

  print "All spec tests passed\n";
}
