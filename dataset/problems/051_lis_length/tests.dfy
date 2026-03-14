// Longest Increasing Subsequence Length -- Runtime spec tests
// Note: IsSubsequence is a ghost predicate (uses existential quantifier over
// witness sequences), so it cannot be executed at runtime. We test
// IsStrictlyIncreasing instead.

// ghost predicate IsSubsequence -- cannot test at runtime (skip)

predicate IsStrictlyIncreasing(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
}

method Main() {
  // IsStrictlyIncreasing positive cases
  expect IsStrictlyIncreasing([]), "empty is strictly increasing";
  expect IsStrictlyIncreasing([1]), "singleton is strictly increasing";
  expect IsStrictlyIncreasing([1, 2, 3, 4, 5]), "ascending is strictly increasing";
  expect IsStrictlyIncreasing([1, 3, 5, 7]), "odd numbers strictly increasing";
  expect IsStrictlyIncreasing([-5, 0, 10]), "with negatives strictly increasing";

  // IsStrictlyIncreasing negative cases
  expect !IsStrictlyIncreasing([1, 1]), "equal elements not strictly increasing";
  expect !IsStrictlyIncreasing([3, 2, 1]), "descending not strictly increasing";
  expect !IsStrictlyIncreasing([1, 3, 2]), "dip not strictly increasing";
  expect !IsStrictlyIncreasing([1, 2, 2, 3]), "adjacent equal not strictly increasing";

  // LIS of [3,1,4,1,5,9] is e.g. [1,4,5,9] length 4
  // Verify [1,4,5,9] is strictly increasing
  expect IsStrictlyIncreasing([1, 4, 5, 9]), "LIS candidate is strictly increasing";
  // [3,1,4,1,5,9] itself is not
  expect !IsStrictlyIncreasing([3, 1, 4, 1, 5, 9]), "original not strictly increasing";

  print "All spec tests passed\n";
}
