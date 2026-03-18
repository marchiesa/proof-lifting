function CountChar(s: seq<char>, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

predicate UsesOnlyFirstKLetters(s: seq<char>, k: int)
{
  forall i | 0 <= i < |s| :: 'a' as int <= s[i] as int < 'a' as int + k
}

predicate EachLetterPresent(s: seq<char>, k: int)
{
  forall j | 0 <= j < k :: CountChar(s, ('a' as int + j) as char) >= 1
}

predicate MinFreqIsOptimal(s: seq<char>, n: int, k: int)
  requires k >= 1
{
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

method Main() {
  // === SPEC POSITIVE TESTS ===
  // Ensures predicates hold for correct outputs (small inputs)

  // Scaled from (7,3)->"abcabca" to (3,3)->"abc"
  expect |"abc"| == 3, "spec positive 1a";
  expect UsesOnlyFirstKLetters("abc", 3), "spec positive 1b";
  expect EachLetterPresent("abc", 3), "spec positive 1c";
  expect MinFreqIsOptimal("abc", 3, 3), "spec positive 1d";

  // Scaled from (6,2)->"ababab" to (2,2)->"ab"
  expect |"ab"| == 2, "spec positive 2a";
  expect UsesOnlyFirstKLetters("ab", 2), "spec positive 2b";
  expect EachLetterPresent("ab", 2), "spec positive 2c";
  expect MinFreqIsOptimal("ab", 2, 2), "spec positive 2d";

  // From (1,1)->"a"
  expect |"a"| == 1, "spec positive 3a";
  expect UsesOnlyFirstKLetters("a", 1), "spec positive 3b";
  expect EachLetterPresent("a", 1), "spec positive 3c";
  expect MinFreqIsOptimal("a", 1, 1), "spec positive 3d";

  // Additional small correct: (2,1)->"aa"
  expect |"aa"| == 2, "spec positive 4a";
  expect UsesOnlyFirstKLetters("aa", 1), "spec positive 4b";
  expect EachLetterPresent("aa", 1), "spec positive 4c";
  expect MinFreqIsOptimal("aa", 2, 1), "spec positive 4d";

  // Additional small correct: (3,2)->"aba"
  expect |"aba"| == 3, "spec positive 5a";
  expect UsesOnlyFirstKLetters("aba", 2), "spec positive 5b";
  expect EachLetterPresent("aba", 2), "spec positive 5c";
  expect MinFreqIsOptimal("aba", 3, 2), "spec positive 5d";

  // Additional small correct: (3,1)->"aaa"
  expect |"aaa"| == 3, "spec positive 6a";
  expect UsesOnlyFirstKLetters("aaa", 1), "spec positive 6b";
  expect EachLetterPresent("aaa", 1), "spec positive 6c";
  expect MinFreqIsOptimal("aaa", 3, 1), "spec positive 6d";

  // === SPEC NEGATIVE TESTS ===
  // Ensures predicates reject wrong outputs (small inputs)

  // Scaled from neg1 (6,2) wrong="ababab WRONG": char outside range
  expect !UsesOnlyFirstKLetters("aX", 2), "spec negative 1";

  // Scaled from neg1: wrong length (n=2 but |s|=3)
  expect |"aba"| != 2, "spec negative 2";

  // Scaled from neg2 (1,1) wrong="a WRONG": space outside range
  expect !UsesOnlyFirstKLetters("a ", 1), "spec negative 3";

  // Missing required letter: k=2 but only 'a' present
  expect !EachLetterPresent("aa", 2), "spec negative 4";

  // Char outside range: 'c' not in first 2 letters
  expect !UsesOnlyFirstKLetters("abc", 2), "spec negative 5";

  // Frequency not optimal: n=2, k=1, s="a" -> count('a')=1 < 2/1=2
  expect !MinFreqIsOptimal("a", 2, 1), "spec negative 6";

  // 'b' outside first 1 letter
  expect !UsesOnlyFirstKLetters("b", 1), "spec negative 7";

  // === IMPLEMENTATION TESTS ===
  // Call the method and check correct output (full-size inputs)

  // Test pair 1
  var s1 := UniformString(7, 3);
  expect s1 == "abcabca", "impl test 1 failed";

  var s2 := UniformString(4, 4);
  expect s2 == "abcd", "impl test 2 failed";

  var s3 := UniformString(6, 2);
  expect s3 == "ababab", "impl test 3 failed";

  // Test pair 2: 66 cases of (1,1) -> "a"
  var i := 0;
  while i < 66 {
    var s := UniformString(1, 1);
    expect s == "a", "impl test 4 failed";
    i := i + 1;
  }

  print "All tests passed\n";
}