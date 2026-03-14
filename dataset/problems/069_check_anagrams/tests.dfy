// Check Anagrams -- Runtime spec tests

// The spec: result == (multiset(a) == multiset(b))
// We test the multiset equality predicate directly.

method Main()
{
  // Positive: anagrams
  expect multiset([1, 2, 3]) == multiset([3, 2, 1]),
    "[1,2,3] and [3,2,1] should be anagrams";

  expect multiset([1, 2, 2]) == multiset([2, 1, 2]),
    "[1,2,2] and [2,1,2] should be anagrams";

  expect multiset([1]) == multiset([1]),
    "[1] and [1] should be anagrams";

  var empty: seq<int> := [];
  expect multiset(empty) == multiset(empty),
    "[] and [] should be anagrams";

  expect multiset([5, 5, 5]) == multiset([5, 5, 5]),
    "[5,5,5] and [5,5,5] should be anagrams";

  // Negative: not anagrams
  expect multiset([1, 2]) != multiset([1, 3]),
    "[1,2] and [1,3] should not be anagrams";

  expect multiset([1, 2]) != multiset([1, 2, 3]),
    "Different lengths should not be anagrams";

  expect multiset([1, 1, 2]) != multiset([1, 2, 2]),
    "[1,1,2] and [1,2,2] should not be anagrams (different counts)";

  expect multiset([1]) != multiset([2]),
    "[1] and [2] should not be anagrams";

  expect multiset(empty) != multiset([1]),
    "[] and [1] should not be anagrams";

  print "All spec tests passed\n";
}
