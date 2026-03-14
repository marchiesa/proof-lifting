// Check if Array is a Permutation of 0..n-1 -- Runtime spec tests

predicate IsPermutation(a: seq<int>)
{
  (forall i | 0 <= i < |a| :: 0 <= a[i] < |a|) &&
  (forall i, j | 0 <= i < j < |a| :: a[i] != a[j])
}

method Main() {
  // Positive cases
  expect IsPermutation([]), "empty is a permutation";
  expect IsPermutation([0]), "[0] is a permutation of 0..1";
  expect IsPermutation([0, 1]), "[0,1] is a permutation";
  expect IsPermutation([1, 0]), "[1,0] is a permutation";
  expect IsPermutation([2, 0, 1]), "[2,0,1] is a permutation";
  expect IsPermutation([3, 1, 0, 2]), "[3,1,0,2] is a permutation";

  // Negative: out of range
  expect !IsPermutation([0, 1, 5]), "5 out of range for length 3";
  expect !IsPermutation([1]), "1 out of range for length 1";
  expect !IsPermutation([-1, 0]), "-1 out of range";

  // Negative: duplicates
  expect !IsPermutation([0, 1, 1]), "duplicate 1s";
  expect !IsPermutation([0, 0]), "duplicate 0s";

  print "All spec tests passed\n";
}
