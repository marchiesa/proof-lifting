ghost predicate ValidChars(s: seq<char>)
{
  forall i | 0 <= i < |s| :: s[i] == 'a' || s[i] == 'b' || s[i] == 'c'
}

ghost predicate IsPalindrome(s: seq<char>)
{
  forall i | 0 <= i < |s| / 2 :: s[i] == s[|s| - 1 - i]
}

ghost predicate MaxPalindromeSubstringAtMostK(s: seq<char>, k: int)
{
  forall i, j | 0 <= i < j <= |s| && j - i > k :: !IsPalindrome(s[i..j])
}

method StringGeneration(n: int, k: int) returns (s: seq<char>)
  requires n >= 0
  requires k >= 1
  ensures |s| == n
  ensures ValidChars(s)
  ensures MaxPalindromeSubstringAtMostK(s, k)
{
  var pattern: seq<char> := ['a', 'b', 'c'];
  s := [];
  var i := 0;
  while i < n
  {
    s := s + [pattern[i % 3]];
    i := i + 1;
  }
}

method BuildExpected(n: int) returns (e: seq<char>)
  requires n >= 0
  ensures |e| == n
{
  var pattern: seq<char> := ['a', 'b', 'c'];
  e := [];
  var i := 0;
  while i < n
  {
    e := e + [pattern[i % 3]];
    i := i + 1;
  }
}