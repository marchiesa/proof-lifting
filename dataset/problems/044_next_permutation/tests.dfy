// Next Permutation -- Runtime spec tests
// The IsSortedDesc predicate uses `reads a` (array-based), so we test a seq version.
// Main spec: multiset(a[..]) == old(multiset(a[..])) i.e. permutation is preserved.

predicate IsSortedDescSeq(a: seq<int>)
{
  forall i, j | 0 <= i < j < |a| :: a[i] >= a[j]
}

method Main() {
  // IsSortedDescSeq positive
  expect IsSortedDescSeq([5, 4, 3, 2, 1]), "descending is sorted desc";
  expect IsSortedDescSeq([5, 5, 3, 3, 1]), "non-increasing is sorted desc";
  expect IsSortedDescSeq([]), "empty is sorted desc";
  expect IsSortedDescSeq([42]), "singleton is sorted desc";
  expect IsSortedDescSeq([3, 3, 3]), "all equal is sorted desc";

  // IsSortedDescSeq negative
  expect !IsSortedDescSeq([1, 2, 3]), "ascending is not sorted desc";
  expect !IsSortedDescSeq([1, 3, 2]), "mixed is not sorted desc";

  // Multiset preservation property
  var before := [1, 2, 3];
  var after := [1, 3, 2];  // next permutation of [1,2,3]
  expect multiset(before) == multiset(after), "next permutation preserves multiset";

  var before2 := [3, 2, 1];
  var after2 := [1, 2, 3];  // last permutation wraps to first
  expect multiset(before2) == multiset(after2), "wrapping preserves multiset";

  print "All spec tests passed\n";
}
