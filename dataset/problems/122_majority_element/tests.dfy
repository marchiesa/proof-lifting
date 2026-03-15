// Majority Element -- Test cases

function Count(s: seq<int>, v: int): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == v then 1 else 0) + Count(s[1..], v)
}

predicate IsMajority(s: seq<int>, v: int)
{
  2 * Count(s, v) > |s|
}

method Main()
{
  // Test Count function
  expect Count([], 1) == 0, "Count of empty should be 0";
  expect Count([1, 1, 1], 1) == 3, "Count of [1,1,1] for 1 should be 3";
  expect Count([1, 2, 1], 1) == 2, "Count of [1,2,1] for 1 should be 2";
  expect Count([1, 2, 1], 2) == 1, "Count of [1,2,1] for 2 should be 1";
  expect Count([1, 2, 3], 4) == 0, "Count of [1,2,3] for 4 should be 0";

  // Test IsMajority - positive
  expect IsMajority([1, 1, 1], 1), "1 is majority in [1,1,1]";
  expect IsMajority([1, 2, 1], 1), "1 is majority in [1,2,1]";
  expect IsMajority([3, 3, 3, 1, 2], 3), "3 is majority in [3,3,3,1,2]";

  // Test IsMajority - negative
  expect !IsMajority([1, 2, 3], 1), "1 is not majority in [1,2,3]";
  expect !IsMajority([1, 2, 1, 2], 1), "1 is not majority in [1,2,1,2] (tie)";
  expect !IsMajority([1, 2, 3], 4), "4 is not majority in [1,2,3]";

  print "All spec tests passed\n";
}
