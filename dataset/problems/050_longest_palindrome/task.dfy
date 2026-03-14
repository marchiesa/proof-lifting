// Longest Palindromic Substring (Expand Around Center)
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsPalindrome(s: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |s|
{
  forall k :: 0 <= k < (hi - lo) / 2 ==> s[lo + k] == s[hi - 1 - k]
}

method LongestPalindrome(s: seq<int>) returns (start: int, length: int)
  requires |s| > 0
  ensures 0 <= start
  ensures length > 0
  ensures start + length <= |s|
  ensures IsPalindrome(s, start, start + length)
{
  start := 0;
  length := 1;

  var i := 0;
  while i < |s|
  {
    // Odd-length palindromes centered at i
    var lo := i;
    var hi := i;
    while lo > 0 && hi < |s| - 1 && s[lo - 1] == s[hi + 1]
    {
      lo := lo - 1;
      hi := hi + 1;
    }
    if hi - lo + 1 > length {
      start := lo;
      length := hi - lo + 1;
    }

    // Even-length palindromes centered between i and i+1
    if i + 1 < |s| {
      lo := i;
      hi := i + 1;
      if s[lo] == s[hi] {
        while lo > 0 && hi < |s| - 1 && s[lo - 1] == s[hi + 1]
        {
          lo := lo - 1;
          hi := hi + 1;
        }
        if hi - lo + 1 > length {
          start := lo;
          length := hi - lo + 1;
        }
      }
    }

    i := i + 1;
  }
}
