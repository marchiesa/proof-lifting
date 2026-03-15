// Palindrome Partitioning -- Test cases

predicate IsPalindromeRange(s: seq<char>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |s|
{
  forall i {:trigger s[lo + i]} :: 0 <= i < (hi - lo) / 2 ==> s[lo + i] == s[hi - 1 - i]
}

method Main()
{
  // Test IsPalindromeRange - positive
  expect IsPalindromeRange(['a','b','a'], 0, 3), "aba is palindrome";
  expect IsPalindromeRange(['a','b','b','a'], 0, 4), "abba is palindrome";
  expect IsPalindromeRange(['a'], 0, 1), "a is palindrome";
  expect IsPalindromeRange(['a','b','c'], 0, 0), "empty is palindrome";

  // Test IsPalindromeRange - negative
  expect !IsPalindromeRange(['a','b','c'], 0, 3), "abc not palindrome";
  expect !IsPalindromeRange(['a','b'], 0, 2), "ab not palindrome";

  // Subrange palindrome
  expect IsPalindromeRange(['x','a','b','a','y'], 1, 4), "aba in xabay";

  print "All spec tests passed\n";
}
