// Suffix Array Construction -- Runtime spec tests

predicate IsPermutation(sa: seq<int>, n: int)
{
  |sa| == n &&
  (forall i | 0 <= i < n :: 0 <= sa[i] < n) &&
  (forall i, j | 0 <= i < j < n :: sa[i] != sa[j])
}

method Main() {
  // IsPermutation positive cases
  expect IsPermutation([0], 1), "[0] is perm of size 1";
  expect IsPermutation([0, 1], 2), "[0,1] is perm of size 2";
  expect IsPermutation([1, 0], 2), "[1,0] is perm of size 2";
  expect IsPermutation([2, 0, 1], 3), "[2,0,1] is perm of size 3";
  expect IsPermutation([], 0), "empty is perm of size 0";

  // IsPermutation negative: wrong length
  expect !IsPermutation([0, 1], 3), "length mismatch";
  expect !IsPermutation([0, 1, 2], 2), "too long";

  // IsPermutation negative: out of range
  expect !IsPermutation([0, 3], 2), "3 out of range for n=2";
  expect !IsPermutation([-1, 0], 2), "-1 out of range";

  // IsPermutation negative: duplicates
  expect !IsPermutation([0, 0], 2), "duplicate 0s";
  expect !IsPermutation([1, 1, 0], 3), "duplicate 1s";

  // Suffix array example: s = [2, 1, 3]
  // Suffixes: [2,1,3] at 0, [1,3] at 1, [3] at 2
  // Sorted: [1,3] < [2,1,3] < [3], so sa = [1, 0, 2]
  expect IsPermutation([1, 0, 2], 3), "suffix array of [2,1,3] is valid permutation";

  print "All spec tests passed\n";
}
