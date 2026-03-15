// KMP String Matching -- Test cases

predicate IsMatch(text: seq<char>, pattern: seq<char>, pos: int)
  requires 0 <= pos && pos + |pattern| <= |text|
{
  forall i :: 0 <= i < |pattern| ==> text[pos + i] == pattern[i]
}

predicate ContainsAt(text: seq<char>, pattern: seq<char>, pos: int)
{
  0 <= pos && pos + |pattern| <= |text| && IsMatch(text, pattern, pos)
}

method Main()
{
  // Test IsMatch - positive
  expect IsMatch(['a','b','c','d'], ['b','c'], 1), "bc at pos 1";
  expect IsMatch(['a','b','c'], ['a','b','c'], 0), "Full match at 0";
  expect IsMatch(['a'], ['a'], 0), "Single char match";

  // Test IsMatch - negative
  expect !IsMatch(['a','b','c'], ['b','c'], 0), "bc not at pos 0";
  expect !IsMatch(['a','b','c'], ['a','c'], 0), "ac not at pos 0";

  // Test ContainsAt
  expect ContainsAt(['h','e','l','l','o'], ['e','l'], 1), "el at pos 1";
  expect !ContainsAt(['h','e','l','l','o'], ['e','l'], 0), "el not at pos 0";
  expect !ContainsAt(['h','i'], ['h','i','j'], 0), "Pattern longer than remaining text";

  print "All spec tests passed\n";
}
