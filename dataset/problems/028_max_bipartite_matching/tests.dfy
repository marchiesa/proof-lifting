// Counting Sort -- Runtime spec tests

predicate IsSorted(a: seq<int>)
{
  forall i, j | 0 <= i < j < |a| :: a[i] <= a[j]
}

method Main()
{
  // Test IsSorted
  expect IsSorted([0, 1, 1, 3, 4, 5]), "sorted sequence";
  expect IsSorted([]), "empty is sorted";
  expect IsSorted([0]), "single element sorted";
  expect !IsSorted([3, 1, 4, 1, 5]), "unsorted sequence";
  expect IsSorted([0, 0, 0]), "all zeros sorted";
  expect !IsSorted([1, 0]), "1,0 not sorted";

  // Test multiset preservation concept
  // Sorting [3, 1, 4, 1, 5] should give [1, 1, 3, 4, 5]
  var input := [3, 1, 4, 1, 5];
  var expected := [1, 1, 3, 4, 5];
  expect multiset(input) == multiset(expected),
    "multiset of input equals multiset of sorted output";
  expect IsSorted(expected), "expected output is sorted";
  expect |input| == |expected|, "length preserved";

  // Test another example
  var input2 := [0, 0, 2, 1, 0];
  var expected2 := [0, 0, 0, 1, 2];
  expect multiset(input2) == multiset(expected2),
    "multiset preserved for second example";
  expect IsSorted(expected2), "second expected output is sorted";

  // Test precondition: all values in [0, maxVal)
  expect 0 <= 3 && 3 < 6, "3 is in range [0,6)";
  expect 0 <= 0 && 0 < 6, "0 is in range [0,6)";
  expect 0 <= 5 && 5 < 6, "5 is in range [0,6)";

  // Test empty case
  var empty: seq<int> := [];
  expect multiset(empty) == multiset(empty), "empty multisets equal";
  expect IsSorted(empty), "empty result is sorted";

  // All same values
  var input3 := [2, 2, 2];
  var expected3 := [2, 2, 2];
  expect multiset(input3) == multiset(expected3), "all same values multiset";
  expect IsSorted(expected3), "all same values sorted";

  print "All spec tests passed\n";
}
