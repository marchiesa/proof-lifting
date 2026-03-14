// Merge Sort -- Runtime spec tests

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

method Main()
{
  // Test IsSorted predicate: positive cases
  var r := IsSortedCheck([1, 2, 3, 4, 5]);
  expect r, "[1,2,3,4,5] should be sorted";

  r := IsSortedCheck([1, 1, 2, 2, 3]);
  expect r, "[1,1,2,2,3] should be sorted";

  r := IsSortedCheck([]);
  expect r, "[] should be sorted";

  r := IsSortedCheck([42]);
  expect r, "[42] should be sorted";

  r := IsSortedCheck([1, 1, 1]);
  expect r, "[1,1,1] should be sorted";

  // Test IsSorted: negative cases
  r := IsSortedCheck([3, 1, 2]);
  expect !r, "[3,1,2] should not be sorted";

  r := IsSortedCheck([5, 4, 3, 2, 1]);
  expect !r, "[5,4,3,2,1] should not be sorted";

  r := IsSortedCheck([1, 3, 2]);
  expect !r, "[1,3,2] should not be sorted";

  // Test multiset preservation (the other postcondition)
  expect multiset([3, 1, 4, 1, 5]) == multiset([1, 1, 3, 4, 5]),
    "multiset of [3,1,4,1,5] should equal multiset of sorted [1,1,3,4,5]";

  expect multiset([5, 4, 3, 2, 1]) == multiset([1, 2, 3, 4, 5]),
    "multiset of reverse should equal multiset of sorted";

  // Negative: multiset should differ if elements differ
  expect multiset([1, 2, 3]) != multiset([1, 2, 4]),
    "Different elements should have different multisets";

  expect multiset([1, 1, 2]) != multiset([1, 2, 2]),
    "Different counts should have different multisets";

  print "All spec tests passed\n";
}
