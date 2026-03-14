// Partition Around Pivot -- Runtime spec tests
// The spec is expressed via the method's postconditions (no standalone predicate).
// We test the partitioning property directly using helper predicates.

predicate AllAtMost(a: seq<int>, lo: int, hi: int, pivot: int)
  requires 0 <= lo <= hi <= |a|
{
  forall i | lo <= i < hi :: a[i] <= pivot
}

predicate AllGreaterThan(a: seq<int>, lo: int, hi: int, pivot: int)
  requires 0 <= lo <= hi <= |a|
{
  forall i | lo <= i < hi :: a[i] > pivot
}

method Main()
{
  // Test AllAtMost
  expect AllAtMost([1, 2, 3], 0, 3, 3), "all <= 3 in [1,2,3]";
  expect AllAtMost([1, 2, 3], 0, 3, 5), "all <= 5 in [1,2,3]";
  expect !AllAtMost([1, 2, 3], 0, 3, 2), "not all <= 2 in [1,2,3]";
  expect AllAtMost([1, 2, 3], 0, 0, 0), "empty range is vacuously true";
  expect AllAtMost([1, 2, 3], 0, 2, 2), "first two elements <= 2";

  // Test AllGreaterThan
  expect AllGreaterThan([5, 6, 7], 0, 3, 4), "all > 4 in [5,6,7]";
  expect !AllGreaterThan([5, 6, 7], 0, 3, 5), "not all > 5 in [5,6,7]";
  expect AllGreaterThan([5, 6, 7], 0, 0, 0), "empty range vacuously true";

  // Test that a correctly partitioned sequence satisfies both halves
  // Partitioned [1, 3, 2, 5, 4] around pivot 3: [1, 3, 2] ++ [5, 4]
  var partitioned := [1, 3, 2, 5, 4];
  expect AllAtMost(partitioned, 0, 3, 3), "left half [1,3,2] all <= 3";
  expect AllGreaterThan(partitioned, 3, 5, 3), "right half [5,4] all > 3";

  // Incorrectly partitioned should fail
  var bad := [1, 5, 2, 3, 4];
  expect !AllAtMost(bad, 0, 3, 3), "bad partition: [1,5,2] not all <= 3";

  // Edge: all elements below pivot
  expect AllAtMost([1, 2, 3], 0, 3, 10), "all elements below high pivot";
  expect AllGreaterThan([1, 2, 3], 3, 3, 10), "empty right half ok";

  // Edge: all elements above pivot
  expect AllAtMost([5, 6, 7], 0, 0, 2), "empty left half ok";
  expect AllGreaterThan([5, 6, 7], 0, 3, 2), "all elements above low pivot";

  print "All spec tests passed\n";
}
