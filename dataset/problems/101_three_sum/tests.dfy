// Three Sum -- Runtime spec tests

// Bounded IsSorted for runtime
function IsSortedBounded(a: seq<int>): bool
{
  if |a| <= 1 then true
  else a[0] <= a[1] && IsSortedBounded(a[1..])
}

method Main()
{
  // IsSorted: positive cases
  expect IsSortedBounded([-1, -1, 0, 1, 2, 4]), "Sorted array";
  expect IsSortedBounded([1, 2, 3]), "Simple sorted";
  expect IsSortedBounded([1, 1, 1]), "All equal is sorted";
  expect IsSortedBounded([]), "Empty is sorted";
  expect IsSortedBounded([42]), "Single element is sorted";

  // IsSorted: negative cases
  expect !IsSortedBounded([3, 2, 1]), "Reverse order is not sorted";
  expect !IsSortedBounded([1, 3, 2]), "Unsorted is not sorted";

  // Test three-sum property manually:
  // For [-1, -1, 0, 1, 2, 4], sum to 0: (-1) + (-1) + 2 = 0
  var a := [-1, -1, 0, 1, 2, 4];
  expect a[0] + a[1] + a[4] == 0, "Triple (-1,-1,2) sums to 0";
  expect 0 < 1 && 1 < 4, "Indices are strictly increasing";

  // Test no triple sums to target
  var b := [1, 2, 3];
  // min sum = 1+2+3 = 6, so no triple sums to 100
  expect b[0] + b[1] + b[2] == 6, "Only triple in [1,2,3] sums to 6";
  expect b[0] + b[1] + b[2] != 100, "No triple sums to 100";

  // Too few elements
  expect |[1, 2]| < 3, "Array of length 2 can't have 3 distinct indices";

  print "All spec tests passed\n";
}
