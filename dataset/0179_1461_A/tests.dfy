predicate ValidChars(s: seq<char>)
{
  forall i | 0 <= i < |s| :: s[i] == 'a' || s[i] == 'b' || s[i] == 'c'
}

predicate IsPalindrome(s: seq<char>)
{
  forall i | 0 <= i < |s| / 2 :: s[i] == s[|s| - 1 - i]
}

predicate MaxPalindromeSubstringAtMostK(s: seq<char>, k: int)
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

method Main()
{
  // ========================================
  // SPEC POSITIVE TESTS (small inputs only)
  // Testing all three ensures predicates on correct outputs
  // ========================================

  // From Test 3: (1,1) -> "a"
  expect |"a"| == 1, "spec positive 1: length";
  expect ValidChars("a"), "spec positive 1: valid chars";
  expect MaxPalindromeSubstringAtMostK("a", 1), "spec positive 1: max palindrome";

  // From Test 3: (2,1) -> "ab"
  expect |"ab"| == 2, "spec positive 2: length";
  expect ValidChars("ab"), "spec positive 2: valid chars";
  expect MaxPalindromeSubstringAtMostK("ab", 1), "spec positive 2: max palindrome";

  // From Test 3: (3,1) -> "abc"
  expect |"abc"| == 3, "spec positive 3: length";
  expect ValidChars("abc"), "spec positive 3: valid chars";
  expect MaxPalindromeSubstringAtMostK("abc", 1), "spec positive 3: max palindrome";

  // From Test 1: (3,2) -> "abc"
  expect |"abc"| == 3, "spec positive 4: length";
  expect ValidChars("abc"), "spec positive 4: valid chars";
  expect MaxPalindromeSubstringAtMostK("abc", 2), "spec positive 4: max palindrome";

  // From Test 1/3: (4,1) -> "abca"
  expect |"abca"| == 4, "spec positive 5: length";
  expect ValidChars("abca"), "spec positive 5: valid chars";
  expect MaxPalindromeSubstringAtMostK("abca", 1), "spec positive 5: max palindrome";

  // From Test 3: (5,1) -> "abcab"
  expect |"abcab"| == 5, "spec positive 6: length";
  expect ValidChars("abcab"), "spec positive 6: valid chars";
  expect MaxPalindromeSubstringAtMostK("abcab", 1), "spec positive 6: max palindrome";

  // From Test 4: (4,4) -> "abca"
  expect |"abca"| == 4, "spec positive 7: length";
  expect ValidChars("abca"), "spec positive 7: valid chars";
  expect MaxPalindromeSubstringAtMostK("abca", 4), "spec positive 7: max palindrome";

  // From Test 4: (5,2) -> "abcab"
  expect |"abcab"| == 5, "spec positive 8: length";
  expect ValidChars("abcab"), "spec positive 8: valid chars";
  expect MaxPalindromeSubstringAtMostK("abcab", 2), "spec positive 8: max palindrome";

  // From Test 4: (5,3) -> "abcab"
  expect |"abcab"| == 5, "spec positive 9: length";
  expect ValidChars("abcab"), "spec positive 9: valid chars";
  expect MaxPalindromeSubstringAtMostK("abcab", 3), "spec positive 9: max palindrome";

  // ========================================
  // SPEC NEGATIVE TESTS (small inputs only)
  // Each scaled down from a negative test pair; at least one ensures predicate must fail
  // ========================================

  // Negative 1: (4,1) wrong output "abca WRONG"
  // Scaled down: (2,1) with "aa" - palindrome "aa" of length 2 > 1 violates spec
  expect !(|"aa"| == 2 && ValidChars("aa") && MaxPalindromeSubstringAtMostK("aa", 1)), "spec negative 1";

  // Negative 2: (1000,1000) wrong output (appended WRONG -> wrong length/chars)
  // Scaled down: (3,1) with "aba" - palindrome "aba" of length 3 > 1
  expect !(|"aba"| == 3 && ValidChars("aba") && MaxPalindromeSubstringAtMostK("aba", 1)), "spec negative 2";

  // Negative 3: (10,1) wrong output
  // Scaled down: (3,1) with "aab" - palindrome "aa" of length 2 > 1
  expect !(|"aab"| == 3 && ValidChars("aab") && MaxPalindromeSubstringAtMostK("aab", 1)), "spec negative 3";

  // Negative 4: (10,1) wrong output
  // Scaled down: (3,2) with "aba" - palindrome "aba" of length 3 > 2
  expect !(|"aba"| == 3 && ValidChars("aba") && MaxPalindromeSubstringAtMostK("aba", 2)), "spec negative 4";

  // Negative 5: (861,1) wrong output (wrong length from WRONG suffix)
  // Scaled down: (2,1) with "abc" - wrong length (3 != 2)
  expect !(|"abc"| == 2 && ValidChars("abc") && MaxPalindromeSubstringAtMostK("abc", 1)), "spec negative 5";

  // Negative 6: (674,123) wrong output
  // Scaled down: (1,1) with "ab" - wrong length (2 != 1)
  expect !(|"ab"| == 1 && ValidChars("ab") && MaxPalindromeSubstringAtMostK("ab", 1)), "spec negative 6";

  // Negative 7: (20,1) wrong output
  // Scaled down: (3,1) with "abb" - palindrome "bb" of length 2 > 1
  expect !(|"abb"| == 3 && ValidChars("abb") && MaxPalindromeSubstringAtMostK("abb", 1)), "spec negative 7";

  // Negative 8: (30,1) wrong output
  // Scaled down: (2,1) with "bb" - palindrome "bb" of length 2 > 1
  expect !(|"bb"| == 2 && ValidChars("bb") && MaxPalindromeSubstringAtMostK("bb", 1)), "spec negative 8";

  // Negative 9: (999,1) wrong output
  // Scaled down: (3,1) with "cbc" - palindrome "cbc" of length 3 > 1
  expect !(|"cbc"| == 3 && ValidChars("cbc") && MaxPalindromeSubstringAtMostK("cbc", 1)), "spec negative 9";

  // Negative 10: (888,887) wrong output
  // Scaled down: (3,2) with "bab" - palindrome "bab" of length 3 > 2
  expect !(|"bab"| == 3 && ValidChars("bab") && MaxPalindromeSubstringAtMostK("bab", 2)), "spec negative 10";

  // ========================================
  // IMPLEMENTATION TESTS (full-size test pairs)
  // ========================================
  var tests: seq<(int, int)> := [
    // Test 1
    (3, 2), (4, 1),
    // Test 2
    (1000, 1), (1000, 2), (1000, 3), (1000, 4), (1000, 5),
    (999, 1), (875, 7), (1000, 123), (921, 129), (1000, 1000),
    // Test 3
    (1, 1), (2, 1), (3, 1), (4, 1), (5, 1),
    (6, 1), (7, 1), (8, 1), (9, 1), (10, 1),
    // Test 4
    (123, 23), (4, 4), (5, 1), (5, 2), (5, 3),
    (7, 2), (7, 1), (7, 7), (10, 9), (10, 1),
    // Test 5
    (852, 1), (853, 1), (854, 1), (855, 1), (856, 1),
    (857, 1), (858, 1), (859, 1), (860, 1), (861, 1),
    // Test 6
    (567, 1), (234, 2), (543, 1), (888, 1), (864, 2),
    (123, 3), (543, 1), (333, 1), (999, 1), (674, 123),
    // Test 7
    (11, 1), (12, 1), (13, 1), (14, 1), (15, 1),
    (16, 1), (17, 1), (18, 1), (19, 1), (20, 1),
    // Test 8
    (21, 1), (22, 1), (23, 1), (24, 1), (25, 1),
    (26, 1), (27, 1), (28, 1), (29, 1), (30, 1),
    // Test 9
    (1000, 1), (991, 1), (992, 1), (993, 1), (994, 1),
    (995, 1), (996, 1), (997, 1), (998, 1), (999, 1),
    // Test 10
    (543, 2), (345, 1), (433, 234), (678, 12), (194, 47),
    (55, 3), (45, 1), (999, 1), (784, 1), (888, 887),
    // Test 11
    (543, 1), (123, 1), (538, 1), (765, 1), (712, 1),
    (543, 1), (888, 1), (994, 1), (333, 1), (679, 12),
    // Test 12
    (101, 1), (102, 1), (103, 1), (104, 1), (105, 1),
    (106, 1), (107, 1), (108, 1), (109, 1), (110, 1),
    // Test 13
    (201, 1), (202, 1), (203, 1), (204, 1), (205, 1),
    (206, 1), (207, 1), (208, 1), (209, 1), (210, 1),
    // Test 14
    (501, 1), (502, 1), (503, 1), (504, 1), (505, 1),
    (506, 1), (507, 1), (508, 1), (509, 1), (510, 1)
  ];

  var i := 0;
  while i < |tests|
  {
    var n := tests[i].0;
    var k := tests[i].1;
    var result := StringGeneration(n, k);
    var expected := BuildExpected(n);
    expect |result| == n, "impl test: wrong length";
    expect result == expected, "impl test: wrong output";
    i := i + 1;
  }

  print "All tests passed\n";
}