// Longest Common Subsequence -- Runtime spec tests

// Copy spec functions from task.dfy
function Max(x: int, y: int): int { if x >= y then x else y }

function LCSLen(a: seq<int>, b: seq<int>): nat
  decreases |a|, |b|
{
  if |a| == 0 || |b| == 0 then 0
  else if a[|a|-1] == b[|b|-1] then 1 + LCSLen(a[..|a|-1], b[..|b|-1])
  else Max(LCSLen(a[..|a|-1], b), LCSLen(a, b[..|b|-1]))
}

method Main()
{
  // Test 1: identical sequences
  expect LCSLen([1, 2, 3], [1, 2, 3]) == 3, "LCS of identical seqs should be 3";

  // Test 2: one empty
  expect LCSLen([], [1, 2]) == 0, "LCS with empty should be 0";
  expect LCSLen([1, 2], []) == 0, "LCS with empty should be 0";

  // Test 3: both empty
  var empty: seq<int> := [];
  expect LCSLen(empty, empty) == 0, "LCS of both empty should be 0";

  // Test 4: no common elements
  expect LCSLen([1, 2, 3], [4, 5, 6]) == 0, "LCS with no common elements should be 0";

  // Test 5: classic example
  // LCS of [1,3,4,5,6,7,8] and [3,5,7] should be 3
  expect LCSLen([1, 3, 4, 5, 6, 7, 8], [3, 5, 7]) == 3, "LCS should be 3";

  // Test 6: single common element
  expect LCSLen([1, 2, 3], [4, 2, 5]) == 1, "LCS should be 1";

  // Test 7: subsequence at start
  expect LCSLen([1, 2, 3, 4], [1, 2]) == 2, "LCS should be 2";

  // Test 8: subsequence at end
  expect LCSLen([1, 2, 3], [3]) == 1, "LCS should be 1";

  // Negative tests
  expect LCSLen([1, 2, 3], [1, 2, 3]) != 2, "LCS of [1,2,3] and [1,2,3] should not be 2";
  expect LCSLen([1, 2, 3], [4, 5, 6]) != 1, "LCS with no common should not be 1";

  print "All spec tests passed\n";
}
