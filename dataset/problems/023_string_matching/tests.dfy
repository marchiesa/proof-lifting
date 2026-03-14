// String Matching (Naive) -- Runtime spec tests

// Compilable version of MatchAt (the original has preconditions that are fine)
predicate MatchAt(text: seq<int>, pattern: seq<int>, pos: int)
  requires |pattern| > 0
  requires 0 <= pos <= |text| - |pattern|
{
  text[pos..pos + |pattern|] == pattern
}

// Helper to check if pattern exists anywhere in text
predicate ContainsPattern(text: seq<int>, pattern: seq<int>)
  requires |pattern| > 0
  requires |pattern| <= |text|
{
  exists k | 0 <= k <= |text| - |pattern| :: MatchAt(text, pattern, k)
}

method Main()
{
  // Test MatchAt
  var text := [1, 2, 3, 4, 5];
  var pat := [3, 4];
  expect MatchAt(text, pat, 2), "pattern [3,4] matches at position 2 in [1,2,3,4,5]";
  expect !MatchAt(text, pat, 0), "pattern [3,4] does not match at position 0";
  expect !MatchAt(text, pat, 1), "pattern [3,4] does not match at position 1";
  expect !MatchAt(text, pat, 3), "pattern [3,4] does not match at position 3";

  // Test with pattern at beginning
  expect MatchAt([1, 2, 3], [1, 2], 0), "[1,2] matches at position 0 in [1,2,3]";
  expect !MatchAt([1, 2, 3], [1, 2], 1), "[1,2] does not match at position 1";

  // Test with pattern at end
  expect MatchAt([1, 2, 3], [2, 3], 1), "[2,3] matches at position 1 in [1,2,3]";

  // Test full match
  expect MatchAt([1, 2, 3], [1, 2, 3], 0), "full text match";

  // Test single element pattern
  expect MatchAt([1, 2, 3], [2], 1), "single element pattern at pos 1";
  expect !MatchAt([1, 2, 3], [2], 0), "single element pattern not at pos 0";

  // Test ContainsPattern
  expect ContainsPattern([1, 2, 3, 4, 5], [3, 4]), "text contains [3,4]";
  expect !ContainsPattern([1, 2, 3], [4, 5]), "text does not contain [4,5]";
  expect ContainsPattern([1, 2, 3], [1, 2, 3]), "text contains itself";
  expect ContainsPattern([1, 1, 1], [1, 1]), "repeated pattern found";

  print "All spec tests passed\n";
}
