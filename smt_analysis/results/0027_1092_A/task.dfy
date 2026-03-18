ghost function CountChar(s: seq<char>, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

ghost predicate UsesOnlyFirstKLetters(s: seq<char>, k: int)
{
  forall i | 0 <= i < |s| :: 'a' as int <= s[i] as int < 'a' as int + k
}

ghost predicate EachLetterPresent(s: seq<char>, k: int)
{
  forall j | 0 <= j < k :: CountChar(s, ('a' as int + j) as char) >= 1
}

ghost predicate MinFreqIsOptimal(s: seq<char>, n: int, k: int)
  requires k >= 1
{
  // floor(n/k) is the theoretical maximum for the minimum frequency
  // across k letters in a string of length n, so asserting each
  // letter appears at least floor(n/k) times means the minimum
  // frequency is maximized.
  forall j | 0 <= j < k :: CountChar(s, ('a' as int + j) as char) >= n / k
}

method UniformString(n: int, k: int) returns (s: seq<char>)
  requires 1 <= k <= 26
  requires n >= k
  ensures |s| == n
  ensures UsesOnlyFirstKLetters(s, k)
  ensures EachLetterPresent(s, k)
  ensures MinFreqIsOptimal(s, n, k)
{
  var pattern: seq<char> := [];
  var i := 0;
  while i < k {
    pattern := pattern + [('a' as int + i) as char];
    i := i + 1;
  }
  s := [];
  while |s| < n {
    s := s + pattern;
  }
  s := s[..n];
}