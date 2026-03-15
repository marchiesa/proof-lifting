// Two Sum (Two Pointer) -- Test cases

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate HasPairSum(a: seq<int>, target: int)
{
  exists i, j :: 0 <= i < j < |a| && a[i] + a[j] == target
}

method Main()
{
  // Test IsSorted
  expect IsSorted([1, 2, 3, 4, 5]), "[1..5] is sorted";
  expect !IsSorted([1, 3, 2]), "[1,3,2] not sorted";

  // Test HasPairSum - positive
  expect HasPairSum([1, 2, 3, 4, 5], 5), "1+4=5 in [1..5]";
  expect HasPairSum([1, 2, 3, 4, 5], 9), "4+5=9 in [1..5]";
  expect HasPairSum([1, 3], 4), "1+3=4";

  // Test HasPairSum - negative
  expect !HasPairSum([1, 2, 3], 10), "No pair sums to 10 in [1,2,3]";
  expect !HasPairSum([1], 2), "Single element has no pair";
  expect !HasPairSum([], 0), "Empty has no pair";
  expect !HasPairSum([1, 2, 3], 2), "No pair sums to 2 in [1,2,3]";

  print "All spec tests passed\n";
}
