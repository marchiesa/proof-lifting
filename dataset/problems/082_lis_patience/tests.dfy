// LIS via Patience Sorting -- Runtime spec tests

// The spec: ensures length <= |a|
// IsSorted predicate is also defined. We test both.

// Bounded compilable version of IsSorted
method IsSortedCheck(s: seq<int>) returns (result: bool)
{
  if |s| <= 1 { return true; }
  var i := 0;
  while i < |s| - 1
  {
    if s[i] > s[i + 1] { return false; }
    i := i + 1;
  }
  return true;
}

// Check the spec: length <= |a|
method CheckLISSpec(length: nat, seqLen: nat) returns (ok: bool)
{
  ok := length <= seqLen;
}

method Main()
{
  // Test IsSorted predicate
  var r := IsSortedCheck([1, 2, 3, 4, 5]);
  expect r, "[1,2,3,4,5] should be sorted";

  r := IsSortedCheck([5, 4, 3, 2, 1]);
  expect !r, "[5,4,3,2,1] should not be sorted";

  r := IsSortedCheck([1, 1, 2, 2, 3]);
  expect r, "[1,1,2,2,3] should be sorted (equal ok)";

  r := IsSortedCheck([1, 3, 2]);
  expect !r, "[1,3,2] should not be sorted";

  r := IsSortedCheck([]);
  expect r, "[] should be sorted";

  r := IsSortedCheck([42]);
  expect r, "[42] should be sorted";

  // Test the postcondition: length <= |a|
  var ok := CheckLISSpec(0, 0);
  expect ok, "LIS 0 for empty seq satisfies <= 0";

  ok := CheckLISSpec(1, 1);
  expect ok, "LIS 1 for single element satisfies <= 1";

  ok := CheckLISSpec(5, 5);
  expect ok, "LIS 5 for sorted 5-element satisfies <= 5";

  ok := CheckLISSpec(1, 5);
  expect ok, "LIS 1 for 5-element satisfies <= 5";

  ok := CheckLISSpec(4, 8);
  expect ok, "LIS 4 for 8-element satisfies <= 8";

  // Negative: length > |a| would violate spec
  ok := CheckLISSpec(6, 5);
  expect !ok, "LIS 6 for 5-element should violate <= 5";

  ok := CheckLISSpec(2, 1);
  expect !ok, "LIS 2 for 1-element should violate <= 1";

  ok := CheckLISSpec(1, 0);
  expect !ok, "LIS 1 for empty should violate <= 0";

  print "All spec tests passed\n";
}
