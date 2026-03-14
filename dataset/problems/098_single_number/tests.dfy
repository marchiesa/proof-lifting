// Single Number -- Runtime spec tests

function CountOccurrences(a: seq<int>, x: int): nat
{
  multiset(a)[x]
}

// Bounded version of InArray for runtime
function InArray(a: seq<int>, x: int): bool
{
  if |a| == 0 then false
  else a[0] == x || InArray(a[1..], x)
}

method Main()
{
  // CountOccurrences: positive cases
  expect CountOccurrences([2, 2, 1], 2) == 2, "Count of 2 in [2,2,1] is 2";
  expect CountOccurrences([2, 2, 1], 1) == 1, "Count of 1 in [2,2,1] is 1";
  expect CountOccurrences([4, 1, 2, 1, 2], 4) == 1, "Count of 4 in [4,1,2,1,2] is 1";
  expect CountOccurrences([4, 1, 2, 1, 2], 1) == 2, "Count of 1 in [4,1,2,1,2] is 2";
  expect CountOccurrences([42], 42) == 1, "Count of 42 in [42] is 1";

  // CountOccurrences: negative cases
  expect CountOccurrences([2, 2, 1], 3) == 0, "Count of 3 in [2,2,1] is 0";
  expect CountOccurrences([], 1) == 0, "Count of 1 in [] is 0";
  expect CountOccurrences([2, 2, 1], 2) != 1, "Count of 2 in [2,2,1] is not 1";

  // IsUnique-like tests using CountOccurrences
  // Positive: element appears exactly once
  expect CountOccurrences([2, 2, 1], 1) == 1 && InArray([2, 2, 1], 1),
    "1 is unique in [2,2,1]";
  expect CountOccurrences([4, 1, 2, 1, 2], 4) == 1 && InArray([4, 1, 2, 1, 2], 4),
    "4 is unique in [4,1,2,1,2]";

  // Negative: element appears more than once (not unique)
  expect !(CountOccurrences([2, 2, 1], 2) == 1), "2 is not unique in [2,2,1]";
  expect !(CountOccurrences([4, 1, 2, 1, 2], 1) == 1), "1 is not unique in [4,1,2,1,2]";

  // Negative: element doesn't appear at all
  expect !InArray([2, 2, 1], 5), "5 is not in [2,2,1]";

  print "All spec tests passed\n";
}
