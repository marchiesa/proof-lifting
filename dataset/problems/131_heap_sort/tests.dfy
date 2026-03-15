// Heap Sort -- Test cases

predicate IsSortedSeq(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method Main()
{
  // Test IsSortedSeq - positive
  expect IsSortedSeq([]), "Empty sorted";
  expect IsSortedSeq([1]), "Single sorted";
  expect IsSortedSeq([1, 2, 3, 4, 5]), "Ascending sorted";
  expect IsSortedSeq([1, 1, 2, 2, 3]), "With duplicates sorted";

  // Test IsSortedSeq - negative
  expect !IsSortedSeq([3, 1]), "Descending not sorted";
  expect !IsSortedSeq([1, 3, 2]), "Out of order not sorted";

  // Test sorting + permutation spec
  var input := [3, 1, 4, 1, 5];
  var expected := [1, 1, 3, 4, 5];
  expect IsSortedSeq(expected);
  expect multiset(input) == multiset(expected);
  expect multiset(input) != multiset([1, 1, 3, 4, 6]), "Wrong answer fails multiset";
  expect !IsSortedSeq([1, 3, 1, 4, 5]), "Unsorted fails check";

  print "All spec tests passed\n";
}
