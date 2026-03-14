// Intersection of Two Arrays -- Runtime spec tests

// Bounded version for runtime checking
function InSeqBounded(a: seq<int>, x: int): bool
{
  if |a| == 0 then false
  else a[0] == x || InSeqBounded(a[1..], x)
}

function NoDuplicatesBounded(a: seq<int>): bool
{
  if |a| == 0 then true
  else !InSeqBounded(a[1..], a[0]) && NoDuplicatesBounded(a[1..])
}

function IsSubsetOfBounded(a: seq<int>, b: seq<int>): bool
{
  if |a| == 0 then true
  else InSeqBounded(b, a[0]) && IsSubsetOfBounded(a[1..], b)
}

method Main()
{
  // InSeqBounded: positive
  expect InSeqBounded([1, 2, 3], 2), "2 is in [1,2,3]";
  expect InSeqBounded([1, 2, 3], 1), "1 is in [1,2,3]";
  expect InSeqBounded([1, 2, 3], 3), "3 is in [1,2,3]";

  // InSeqBounded: negative
  expect !InSeqBounded([1, 2, 3], 4), "4 is not in [1,2,3]";
  expect !InSeqBounded([], 1), "1 is not in []";

  // NoDuplicatesBounded: positive
  expect NoDuplicatesBounded([1, 2, 3]), "[1,2,3] has no duplicates";
  expect NoDuplicatesBounded([]), "[] has no duplicates";
  expect NoDuplicatesBounded([42]), "[42] has no duplicates";

  // NoDuplicatesBounded: negative
  expect !NoDuplicatesBounded([1, 2, 1]), "[1,2,1] has duplicates";
  expect !NoDuplicatesBounded([2, 2]), "[2,2] has duplicates";

  // IsSubsetOfBounded: positive
  expect IsSubsetOfBounded([2], [1, 2, 3]), "[2] is subset of [1,2,3]";
  expect IsSubsetOfBounded([1, 3], [1, 2, 3]), "[1,3] is subset of [1,2,3]";
  expect IsSubsetOfBounded([], [1, 2, 3]), "[] is subset of anything";

  // IsSubsetOfBounded: negative
  expect !IsSubsetOfBounded([4], [1, 2, 3]), "[4] is not subset of [1,2,3]";
  expect !IsSubsetOfBounded([1, 4], [1, 2, 3]), "[1,4] is not subset of [1,2,3]";

  // Combined spec: intersection properties
  // For [1,2,2,1] and [2,2], intersection should contain 2
  var a := [1, 2, 2, 1];
  var b := [2, 2];
  expect InSeqBounded(a, 2) && InSeqBounded(b, 2),
    "2 is in both arrays so should be in intersection";

  // For [1,2,3] and [4,5,6], no common elements
  expect !InSeqBounded([4, 5, 6], 1) && !InSeqBounded([4, 5, 6], 2) && !InSeqBounded([4, 5, 6], 3),
    "No elements of [1,2,3] are in [4,5,6]";

  print "All spec tests passed\n";
}
