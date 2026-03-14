// Longest Palindromic Substring -- Test cases

predicate IsPalin(s: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |s|
{
  forall k :: 0 <= k < (hi - lo) / 2 ==> s[lo + k] == s[hi - 1 - k]
}

method {:axiom} LongestPalindrome(s: seq<int>) returns (start: int, length: int)
  requires |s| > 0
  ensures 0 <= start
  ensures length > 0
  ensures start + length <= |s|
  ensures IsPalin(s, start, start + length)

method TestPalindrome()
{
  var st, ln := LongestPalindrome([1, 2, 3, 2, 1]);
  assert IsPalin([1, 2, 3, 2, 1], st, st + ln);
  assert ln > 0;
}

method TestSingle()
{
  var st, ln := LongestPalindrome([42]);
  assert ln > 0;
  assert st + ln <= 1;
}

method TestAllSame()
{
  var st, ln := LongestPalindrome([5, 5, 5, 5]);
  assert IsPalin([5, 5, 5, 5], st, st + ln);
}

method TestNoPalin()
{
  var st, ln := LongestPalindrome([1, 2, 3, 4]);
  assert ln > 0;
}
