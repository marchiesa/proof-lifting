// Remove Consecutive Duplicates -- Test cases

predicate NoConsecutiveDups(s: seq<int>)
{
  forall i :: 0 < i < |s| ==> s[i] != s[i-1]
}

method Main()
{
  // Test NoConsecutiveDups - positive
  expect NoConsecutiveDups([]), "Empty has no consecutive dups";
  expect NoConsecutiveDups([1]), "Single element";
  expect NoConsecutiveDups([1, 2, 3]), "All different";
  expect NoConsecutiveDups([1, 2, 1]), "Alternating";
  expect NoConsecutiveDups([1, 2, 1, 2]), "Alternating pattern";

  // Test NoConsecutiveDups - negative
  expect !NoConsecutiveDups([1, 1]), "Two same";
  expect !NoConsecutiveDups([1, 2, 2, 3]), "Consecutive dups in middle";
  expect !NoConsecutiveDups([1, 1, 2, 3]), "Consecutive dups at start";
  expect !NoConsecutiveDups([1, 2, 3, 3]), "Consecutive dups at end";

  print "All spec tests passed\n";
}
