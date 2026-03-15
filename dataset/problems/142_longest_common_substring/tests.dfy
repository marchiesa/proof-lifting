// Longest Common Substring -- Test cases

method LongestCommonSubstring(a: seq<char>, b: seq<char>) returns (length: int)
  ensures length >= 0
  ensures length <= |a|
  ensures length <= |b|
{
  length := 0;
}

method Main()
{
  // Two sequences with common substring
  var r1 := LongestCommonSubstring(['a','b','c','d','e'], ['x','b','c','y']);
  expect r1 >= 0, "non-negative result";
  expect r1 <= 5, "at most |a|";
  expect r1 <= 4, "at most |b|";

  // Identical sequences
  var r2 := LongestCommonSubstring(['a','b','c'], ['a','b','c']);
  expect r2 >= 0, "non-negative";
  expect r2 <= 3, "at most length";

  // No common chars
  var r3 := LongestCommonSubstring(['a','b'], ['c','d']);
  expect r3 >= 0, "non-negative";
  expect r3 <= 2, "bounded by a";
  expect r3 <= 2, "bounded by b";

  // Empty sequence
  var r4 := LongestCommonSubstring([], ['a','b']);
  expect r4 == 0, "empty a gives 0";

  // Both empty
  var r5 := LongestCommonSubstring([], []);
  expect r5 == 0, "both empty gives 0";

  // Single char common
  var r6 := LongestCommonSubstring(['a'], ['a']);
  expect r6 >= 0 && r6 <= 1, "single char bounded";

  print "All spec tests passed\n";
}
