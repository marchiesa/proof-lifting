// String Reversal -- Test cases

predicate IsReverse(s: seq<char>, r: seq<char>)
{
  |r| == |s| && forall i :: 0 <= i < |s| ==> r[i] == s[|s| - 1 - i]
}

method Main()
{
  // Test IsReverse - positive
  expect IsReverse([], []), "Empty reverse";
  expect IsReverse(['a'], ['a']), "Single char reverse";
  expect IsReverse(['a', 'b', 'c'], ['c', 'b', 'a']), "abc -> cba";
  expect IsReverse(['h', 'e', 'l', 'l', 'o'], ['o', 'l', 'l', 'e', 'h']), "hello -> olleh";

  // Test IsReverse - negative
  expect !IsReverse(['a', 'b'], ['a', 'b']), "ab != ab reversed (should be ba)";
  expect !IsReverse(['a', 'b', 'c'], ['a', 'b', 'c']), "abc is not its own reverse";
  expect !IsReverse(['a', 'b'], ['b']), "Wrong length";

  // Palindrome: reverse equals self
  expect IsReverse(['a', 'b', 'a'], ['a', 'b', 'a']), "aba is palindrome";

  print "All spec tests passed\n";
}
