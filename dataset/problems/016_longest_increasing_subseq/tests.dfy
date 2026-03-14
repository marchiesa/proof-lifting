// Longest Increasing Subsequence Length -- Runtime spec tests

// A subsequence witness: indices into `a` forming a strictly increasing subsequence
predicate IsIncreasingSubseq(a: seq<int>, indices: seq<int>)
{
  |indices| > 0 &&
  (forall k | 0 <= k < |indices| :: 0 <= indices[k] < |a|) &&
  (forall k, l | 0 <= k < l < |indices| :: indices[k] < indices[l]) &&
  (forall k, l | 0 <= k < l < |indices| :: a[indices[k]] < a[indices[l]])
}

method Main()
{
  // Test IsIncreasingSubseq - positive cases
  var a := [10, 9, 2, 5, 3, 7, 101, 18];

  // [2, 5, 7, 101] at indices [2, 3, 5, 6] is an increasing subsequence
  expect IsIncreasingSubseq(a, [2, 3, 5, 6]),
    "indices [2,3,5,6] give values [2,5,7,101] - valid LIS";

  // [2, 3, 7, 18] at indices [2, 4, 5, 7]
  expect IsIncreasingSubseq(a, [2, 4, 5, 7]),
    "indices [2,4,5,7] give values [2,3,7,18] - valid LIS";

  // Single element is a valid subsequence
  expect IsIncreasingSubseq(a, [0]), "single index is valid";
  expect IsIncreasingSubseq(a, [3]), "single index [3] is valid";

  // Two element subsequence
  expect IsIncreasingSubseq(a, [2, 3]), "[2,3] gives values [2,5] - valid";

  // Test IsIncreasingSubseq - negative cases
  // Empty is not valid (requires |indices| > 0)
  // Reversed indices should fail
  expect !IsIncreasingSubseq(a, [3, 2]), "indices must be increasing";

  // Values not increasing
  expect !IsIncreasingSubseq(a, [0, 1]), "[0,1] gives [10,9] - not increasing";

  // Test on strictly increasing array
  var b := [1, 2, 3, 4, 5];
  expect IsIncreasingSubseq(b, [0, 1, 2, 3, 4]), "full array is LIS when sorted";
  expect IsIncreasingSubseq(b, [0, 2, 4]), "[1,3,5] is valid subseq";

  // Test on strictly decreasing array
  var c := [5, 4, 3, 2, 1];
  expect IsIncreasingSubseq(c, [4]), "only single elements work for decreasing";
  expect !IsIncreasingSubseq(c, [0, 1]), "[5,4] not increasing";

  print "All spec tests passed\n";
}
