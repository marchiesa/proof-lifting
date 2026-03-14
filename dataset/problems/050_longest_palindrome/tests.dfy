// Longest Palindromic Substring -- Runtime spec tests

predicate IsPalindrome(s: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |s|
{
  forall k {:trigger s[lo + k]} | 0 <= k < (hi - lo) / 2 :: s[lo + k] == s[hi - 1 - k]
}

method Main() {
  // IsPalindrome positive cases
  var s1 := [1, 2, 3, 2, 1];
  expect IsPalindrome(s1, 0, 5), "[1,2,3,2,1] is palindrome";
  expect IsPalindrome(s1, 1, 4), "[2,3,2] is palindrome";
  expect IsPalindrome(s1, 2, 3), "[3] singleton is palindrome";
  expect IsPalindrome(s1, 0, 0), "empty range is palindrome";

  var s2 := [5, 5, 5, 5];
  expect IsPalindrome(s2, 0, 4), "all same is palindrome";
  expect IsPalindrome(s2, 0, 2), "prefix of all-same is palindrome";

  var s3 := [1, 2, 2, 1];
  expect IsPalindrome(s3, 0, 4), "[1,2,2,1] even palindrome";

  // IsPalindrome negative cases
  var s4 := [1, 2, 3, 4];
  expect !IsPalindrome(s4, 0, 4), "[1,2,3,4] is not palindrome";
  expect !IsPalindrome(s4, 0, 3), "[1,2,3] is not palindrome";

  var s5 := [1, 2, 1, 3];
  expect !IsPalindrome(s5, 0, 4), "[1,2,1,3] is not palindrome";

  // Single element is always palindrome
  expect IsPalindrome([42], 0, 1), "single element palindrome";

  print "All spec tests passed\n";
}
