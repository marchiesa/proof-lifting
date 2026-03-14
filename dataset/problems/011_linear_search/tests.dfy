// Linear Search -- Runtime spec tests
// The spec is in postconditions. We test the relevant properties directly.
// The key spec concept: "first index where a[index] > threshold"

predicate AllBelowThreshold(a: seq<int>, hi: int, threshold: int)
  requires 0 <= hi <= |a|
{
  forall k | 0 <= k < hi :: a[k] <= threshold
}

predicate ExistsAboveThreshold(a: seq<int>, threshold: int)
{
  exists k | 0 <= k < |a| :: a[k] > threshold
}

method Main()
{
  // Test AllBelowThreshold
  expect AllBelowThreshold([1, 2, 3], 3, 3), "all of [1,2,3] <= 3";
  expect AllBelowThreshold([1, 2, 3], 3, 10), "all of [1,2,3] <= 10";
  expect !AllBelowThreshold([1, 2, 3], 3, 2), "not all of [1,2,3] <= 2";
  expect AllBelowThreshold([1, 2, 3], 0, 0), "empty prefix vacuously true";
  expect AllBelowThreshold([], 0, 0), "empty array vacuously true";

  // Test ExistsAboveThreshold
  expect ExistsAboveThreshold([1, 3, 5, 7], 4), "5 and 7 are above 4";
  expect !ExistsAboveThreshold([1, 2, 3], 10), "nothing above 10 in [1,2,3]";
  expect !ExistsAboveThreshold([], 0), "empty has nothing above anything";
  expect ExistsAboveThreshold([5, 1, 2], 0), "5 is above 0";

  // Test combined: for [1, 3, 5, 7] with threshold 4:
  // first element > 4 is at index 2 (value 5)
  var a := [1, 3, 5, 7];
  expect AllBelowThreshold(a, 2, 4), "elements before index 2 are all <= 4";
  expect a[2] > 4, "element at index 2 is above threshold";
  expect !AllBelowThreshold(a, 3, 4), "elements before index 3 not all <= 4";

  // No match case
  expect AllBelowThreshold([1, 2, 3], 3, 10), "all elements <= 10";
  expect !ExistsAboveThreshold([1, 2, 3], 10), "no element > 10";

  print "All spec tests passed\n";
}
