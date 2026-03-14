// Majority Element -- Runtime spec tests

function Count(a: seq<int>, val: int): nat
{
  if |a| == 0 then 0
  else (if a[0] == val then 1 else 0) + Count(a[1..], val)
}

predicate IsMajority(a: seq<int>, val: int)
{
  2 * Count(a, val) > |a|
}

method Main() {
  // Count function tests
  expect Count([], 1) == 0, "count in empty is 0";
  expect Count([1], 1) == 1, "count of 1 in [1] is 1";
  expect Count([1, 2, 1], 1) == 2, "count of 1 in [1,2,1] is 2";
  expect Count([1, 2, 3], 4) == 0, "count of absent element is 0";
  expect Count([3, 3, 3, 2, 1], 3) == 3, "count of 3 in [3,3,3,2,1] is 3";
  expect Count([5, 5, 5, 5], 5) == 4, "count of 5 in all-fives is 4";

  // IsMajority positive cases
  expect IsMajority([3, 3, 3, 2, 1], 3), "3 is majority of [3,3,3,2,1]";
  expect IsMajority([1], 1), "1 is majority of [1]";
  expect IsMajority([5, 5, 5, 5], 5), "5 is majority of all-fives";
  expect IsMajority([1, 1, 2], 1), "1 is majority of [1,1,2]";

  // IsMajority negative cases
  expect !IsMajority([1, 2, 3], 1), "1 is not majority of [1,2,3]";
  expect !IsMajority([1, 1, 2, 2], 1), "1 is not majority of [1,1,2,2] (tie)";
  expect !IsMajority([3, 3, 3, 2, 1], 2), "2 is not majority";
  expect !IsMajority([], 1), "no majority in empty";

  // Wrong answer check
  expect Count([3, 3, 3, 2, 1], 3) != 2, "count of 3 is not 2";

  print "All spec tests passed\n";
}
