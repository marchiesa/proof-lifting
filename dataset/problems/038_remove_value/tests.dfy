// Remove All Occurrences of Value from Array -- Runtime spec tests
// The spec is in the method postconditions. We test the postcondition properties
// as standalone helper predicates.
// Note: The postcondition `forall x :: x != val ==> multiset(result)[x] == multiset(a)[x]`
// uses an unbounded quantifier. We test it on specific elements instead.

predicate NoVal(result: seq<int>, val: int)
{
  forall i | 0 <= i < |result| :: result[i] != val
}

predicate AllFromOriginal(result: seq<int>, a: seq<int>)
{
  forall i | 0 <= i < |result| :: result[i] in a
}

method Main() {
  // NoVal positive
  expect NoVal([1, 3, 5], 2), "no 2s in [1,3,5]";
  expect NoVal([], 5), "empty has no value";
  expect NoVal([1, 2, 3], 4), "no 4s in [1,2,3]";
  expect NoVal([1, 3], 2), "no 2s after removal";

  // NoVal negative
  expect !NoVal([1, 2, 3], 2), "2 is in [1,2,3]";
  expect !NoVal([5, 5, 5], 5), "5 is in [5,5,5]";
  expect !NoVal([1, 2, 1], 1), "1 is in [1,2,1]";

  // AllFromOriginal positive
  expect AllFromOriginal([1, 3], [1, 2, 3]), "[1,3] all from [1,2,3]";
  expect AllFromOriginal([], [1, 2]), "empty all from anything";
  expect AllFromOriginal([1, 1], [1, 2]), "repeated element from original";

  // AllFromOriginal negative
  expect !AllFromOriginal([4], [1, 2, 3]), "4 not from [1,2,3]";
  expect !AllFromOriginal([1, 5], [1, 2, 3]), "5 not from [1,2,3]";

  // Test multiset preservation for specific elements (bounded checks)
  var a := [1, 2, 3, 2, 1];
  var result := [1, 3, 1];  // after removing 2
  expect NoVal(result, 2), "result has no 2s";
  expect multiset(result)[1] == multiset(a)[1], "count of 1 preserved";
  expect multiset(result)[3] == multiset(a)[3], "count of 3 preserved";
  expect AllFromOriginal(result, a), "all result elements from original";

  // Another example: remove all
  var a2 := [7, 7, 7];
  var result2: seq<int> := [];
  expect NoVal(result2, 7), "empty has no 7s";

  print "All spec tests passed\n";
}
