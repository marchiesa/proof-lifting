// Remove Duplicates from Sorted Array -- Runtime spec tests

// Bounded compilable versions of the spec predicates
method IsSortedCheck(a: seq<int>) returns (result: bool)
{
  var i := 0;
  while i < |a|
  {
    var j := i + 1;
    while j < |a|
    {
      if a[i] > a[j] { return false; }
      j := j + 1;
    }
    i := i + 1;
  }
  return true;
}

method StrictlySortedCheck(a: seq<int>) returns (result: bool)
{
  var i := 0;
  while i < |a|
  {
    var j := i + 1;
    while j < |a|
    {
      if a[i] >= a[j] { return false; }
      j := j + 1;
    }
    i := i + 1;
  }
  return true;
}

method AllInSet(a: seq<int>, s: set<int>) returns (result: bool)
{
  var i := 0;
  while i < |a|
  {
    if a[i] !in s { return false; }
    i := i + 1;
  }
  return true;
}

method AllRepresented(original: seq<int>, result: seq<int>) returns (ok: bool)
{
  var i := 0;
  while i < |original|
  {
    var found := false;
    var j := 0;
    while j < |result|
    {
      if result[j] == original[i] { found := true; }
      j := j + 1;
    }
    if !found { return false; }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // Test IsSorted predicate
  var r := IsSortedCheck([1, 2, 3, 4, 5]);
  expect r, "[1,2,3,4,5] should be sorted";

  r := IsSortedCheck([3, 1, 2]);
  expect !r, "[3,1,2] should not be sorted";

  r := IsSortedCheck([1, 1, 2, 2, 3]);
  expect r, "[1,1,2,2,3] should be sorted (non-strict)";

  r := IsSortedCheck([]);
  expect r, "[] should be sorted";

  // Test StrictlySorted predicate
  r := StrictlySortedCheck([1, 2, 3]);
  expect r, "[1,2,3] should be strictly sorted";

  r := StrictlySortedCheck([1, 1, 2]);
  expect !r, "[1,1,2] should NOT be strictly sorted (duplicates)";

  r := StrictlySortedCheck([1, 3, 2]);
  expect !r, "[1,3,2] should NOT be strictly sorted";

  r := StrictlySortedCheck([5]);
  expect r, "[5] should be strictly sorted";

  r := StrictlySortedCheck([]);
  expect r, "[] should be strictly sorted";

  // Test the combined postcondition properties:
  // Given input [1,1,2,2,3], a correct result is [1,2,3] with k=3
  var resultSeq := [1, 2, 3];
  r := StrictlySortedCheck(resultSeq);
  expect r, "Result [1,2,3] should be strictly sorted";

  var origSet: set<int> := {1, 2, 3};
  r := AllInSet(resultSeq, origSet);
  expect r, "All result elements should be in original";

  r := AllRepresented([1, 1, 2, 2, 3], resultSeq);
  expect r, "All original values should be represented in result";

  // Negative: wrong result for [1,1,2,2,3] would be [1,2] (missing 3)
  r := AllRepresented([1, 1, 2, 2, 3], [1, 2]);
  expect !r, "[1,2] does not represent all values from [1,1,2,2,3]";

  // Negative: wrong result [1,1,3] is not strictly sorted
  r := StrictlySortedCheck([1, 1, 3]);
  expect !r, "[1,1,3] is not strictly sorted";

  print "All spec tests passed\n";
}
