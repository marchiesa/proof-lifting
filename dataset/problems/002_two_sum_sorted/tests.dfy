// Two Sum (Sorted Array) -- Runtime spec tests

predicate IsSorted(a: seq<int>)
{
  forall i, j | 0 <= i < j < |a| :: a[i] <= a[j]
}

// HasPairSum uses existential quantifier - need bounded version for compilation
predicate HasPairSum(a: seq<int>, target: int)
{
  exists i, j | 0 <= i < j < |a| :: a[i] + a[j] == target
}

method Main()
{
  // Test IsSorted
  expect IsSorted([1, 2, 3, 4, 6]), "ascending should be sorted";
  expect !IsSorted([6, 4, 3, 2, 1]), "descending should not be sorted";

  // Test HasPairSum - positive cases
  expect HasPairSum([1, 2, 3, 4, 6], 8), "[1,2,3,4,6] should have pair summing to 8 (2+6)";
  expect HasPairSum([1, 2, 3, 4, 6], 3), "[1,2,3,4,6] should have pair summing to 3 (1+2)";
  expect HasPairSum([3, 7], 10), "[3,7] should have pair summing to 10";

  // Test HasPairSum - negative cases
  expect !HasPairSum([1, 2, 3, 4, 6], 20), "[1,2,3,4,6] should not have pair summing to 20";
  expect !HasPairSum([1, 2, 3, 4, 6], 1), "[1,2,3,4,6] should not have pair summing to 1";
  expect !HasPairSum([], 5), "empty should not have pair";
  expect !HasPairSum([5], 10), "single element should not have pair";

  // Edge cases
  expect HasPairSum([1, 1], 2), "[1,1] should have pair summing to 2";
  expect !HasPairSum([1, 2], 5), "[1,2] should not have pair summing to 5";

  print "All spec tests passed\n";
}
