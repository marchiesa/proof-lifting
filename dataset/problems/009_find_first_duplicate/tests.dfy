// Find First Duplicate -- Runtime spec tests

// Compilable version with bounded quantifiers
predicate HasDuplicate(a: seq<int>, idx: int)
  requires 0 <= idx < |a|
{
  exists j | 0 <= j < idx :: a[j] == a[idx]
}

predicate AllDistinctBefore(a: seq<int>, idx: int)
  requires 0 <= idx <= |a|
{
  forall i | 0 <= i < idx :: (forall j | 0 <= j < i :: a[j] != a[i])
}

method Main()
{
  // Test HasDuplicate
  var a1 := [1, 2, 3, 2, 5];
  expect HasDuplicate(a1, 3), "index 3 (value 2) is a duplicate of index 1";
  expect !HasDuplicate(a1, 0), "index 0 has no prior duplicate";
  expect !HasDuplicate(a1, 1), "index 1 (value 2) has no prior duplicate";
  expect !HasDuplicate(a1, 2), "index 2 (value 3) has no prior duplicate";
  expect !HasDuplicate(a1, 4), "index 4 (value 5) has no prior duplicate";

  var a2 := [5, 5];
  expect HasDuplicate(a2, 1), "index 1 is duplicate of index 0";

  // Test AllDistinctBefore
  expect AllDistinctBefore([1, 2, 3, 4], 4), "all distinct sequence";
  expect AllDistinctBefore([1, 2, 3, 2], 3), "distinct before index 3";
  expect !AllDistinctBefore([1, 2, 3, 2], 4), "not all distinct in full sequence";
  expect AllDistinctBefore([], 0), "empty is vacuously distinct";
  expect AllDistinctBefore([42], 1), "single element is distinct";
  expect AllDistinctBefore([1, 2, 3, 2, 5], 3), "distinct before first dup at index 3";
  expect !AllDistinctBefore([1, 2, 3, 2, 5], 4), "not distinct up to index 4";

  // Test combined spec behavior:
  // For a = [1, 2, 3, 2, 5], index 3 should be the first duplicate
  expect HasDuplicate(a1, 3) && AllDistinctBefore(a1, 3),
    "index 3 is first duplicate in [1,2,3,2,5]";

  // For all-distinct, AllDistinctBefore should hold for full length
  expect AllDistinctBefore([1, 2, 3, 4], 4), "[1,2,3,4] is all distinct";

  print "All spec tests passed\n";
}
