// Counting Sort -- Test cases

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate InRange(s: seq<int>, k: int)
{
  forall i :: 0 <= i < |s| ==> 0 <= s[i] < k
}

method Main()
{
  // Test IsSorted predicate - positive cases
  expect IsSorted([]), "Empty should be sorted";
  expect IsSorted([1]), "Single element should be sorted";
  expect IsSorted([1, 2, 3]), "[1,2,3] should be sorted";
  expect IsSorted([1, 1, 2, 3, 3]), "Duplicates should be sorted";

  // Test IsSorted predicate - negative cases
  expect !IsSorted([3, 1]), "[3,1] should not be sorted";
  expect !IsSorted([1, 3, 2]), "[1,3,2] should not be sorted";

  // Test InRange predicate - positive cases
  expect InRange([0, 1, 2], 3), "[0,1,2] should be in range [0,3)";
  expect InRange([], 1), "Empty should be in range";
  expect InRange([0], 1), "[0] should be in range [0,1)";

  // Test InRange predicate - negative cases
  expect !InRange([3], 3), "[3] should not be in range [0,3)";
  expect !InRange([-1], 3), "[-1] should not be in range [0,3)";
  expect !InRange([0, 1, 5], 3), "[0,1,5] should not be in range [0,3)";

  // Test that sorted + permutation is the right spec
  // [2, 0, 1] sorted should be [0, 1, 2]
  var input := [2, 0, 1];
  expect InRange(input, 3);
  expect multiset(input) == multiset([0, 1, 2]);
  expect IsSorted([0, 1, 2]);

  // [1, 0, 1, 0] sorted should be [0, 0, 1, 1]
  var input2 := [1, 0, 1, 0];
  expect InRange(input2, 2);
  expect multiset(input2) == multiset([0, 0, 1, 1]);
  expect IsSorted([0, 0, 1, 1]);

  // Wrong answer should fail multiset check
  expect multiset([2, 0, 1]) != multiset([0, 0, 2]);

  print "All spec tests passed\n";
}
