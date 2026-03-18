// ---- Spec predicates/functions ----

function CountChar(c: char, t: seq<char>): nat
  decreases |t|
{
  if |t| == 0 then 0
  else CountChar(c, t[..|t|-1]) + (if t[|t|-1] == c then 1 else 0)
}

predicate IsSubsequence(t: seq<char>, s: seq<char>)
  decreases |s| + |t|
{
  if |t| == 0 then true
  else if |s| == 0 then false
  else if t[|t|-1] == s[|s|-1] then IsSubsequence(t[..|t|-1], s[..|s|-1])
  else IsSubsequence(t, s[..|s|-1])
}

predicate IsGood(t: seq<char>, k: int)
  requires 1 <= k <= 26
{
  forall i | 0 <= i < k ::
    CountChar(('A' as int + i) as char, t) == CountChar('A', t)
}

predicate HasAtLeastMOfEach(s: seq<char>, k: int, m: int)
  requires 1 <= k <= 26
{
  forall i | 0 <= i < k :: CountChar(('A' as int + i) as char, s) >= m
}

// Combined ensures predicate: all postconditions of LongestGoodSubsequence
predicate MeetsSpec(s: seq<char>, k: int, length: int)
  requires 1 <= k <= 26
{
  length >= 0 &&
  length % k == 0 &&
  HasAtLeastMOfEach(s, k, length / k) &&
  forall m | length / k < m && m <= |s| :: !HasAtLeastMOfEach(s, k, m)
}

// ---- Implementation ----

method LongestGoodSubsequence(s: seq<char>, k: int) returns (length: int)
  requires 1 <= k <= 26
  requires forall i | 0 <= i < |s| :: 'A' <= s[i] && s[i] <= (('A' as int + k - 1) as char)
  ensures length >= 0
  ensures length % k == 0
  ensures HasAtLeastMOfEach(s, k, length / k)
  ensures forall m | length / k < m && m <= |s| :: !HasAtLeastMOfEach(s, k, m)
{
  var upper: seq<char> := [];
  var i := 0;
  var limit := if k < 26 then k else 26;
  while i < limit
  {
    upper := upper + [('A' as int + i) as char];
    i := i + 1;
  }

  if |upper| == 0 {
    length := 0;
    return;
  }

  var counts: seq<int> := [];
  i := 0;
  while i < |upper|
  {
    var count := 0;
    var j := 0;
    while j < |s|
    {
      if s[j] == upper[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    counts := counts + [count];
    i := i + 1;
  }

  var minCount := counts[0];
  i := 1;
  while i < |counts|
  {
    if counts[i] < minCount {
      minCount := counts[i];
    }
    i := i + 1;
  }

  length := minCount * k;
}

// ---- Tests ----

method Main()
{
  // === SPEC POSITIVE TESTS (small inputs, correct outputs) ===
  expect MeetsSpec("A", 1, 1), "spec positive 1";    // Test 10: s="A", k=1, output=1
  expect MeetsSpec("A", 5, 0), "spec positive 2";    // Test 8:  s="A", k=5, output=0
  expect MeetsSpec("BA", 2, 2), "spec positive 3";   // Test 6:  s="BA", k=2, output=2
  expect MeetsSpec("A", 26, 0), "spec positive 4";   // Test 3:  s="A", k=26, output=0
  expect MeetsSpec("AA", 1, 2), "spec positive 5";   // scaled Test 4: k=1, all A's
  expect MeetsSpec("ABC", 3, 3), "spec positive 6";  // scaled Test 7: k=3, one of each
  expect MeetsSpec("AB", 3, 0), "spec positive 7";   // scaled Test 15: missing letter C

  // === SPEC NEGATIVE TESTS (small inputs, wrong outputs) ===
  expect !MeetsSpec("A", 1, 2), "spec negative 1";   // Neg 10: correct=1, wrong=2
  expect !MeetsSpec("A", 5, 1), "spec negative 2";   // Neg 8:  correct=0, wrong=1
  expect !MeetsSpec("BA", 2, 3), "spec negative 3";  // Neg 6:  correct=2, wrong=3
  expect !MeetsSpec("A", 26, 1), "spec negative 4";  // Neg 3:  correct=0, wrong=1
  expect !MeetsSpec("AA", 1, 3), "spec negative 5";  // scaled Neg 4: correct=2, wrong=3
  expect !MeetsSpec("ABC", 3, 4), "spec negative 6"; // scaled Neg 7: correct=3, wrong=4
  expect !MeetsSpec("AB", 3, 1), "spec negative 7";  // scaled Neg 2: correct=0, wrong=1

  // === IMPLEMENTATION TESTS (full-size inputs) ===
  var r1 := LongestGoodSubsequence("ACAABCCAB", 3);
  expect r1 == 6, "impl test 1 failed";

  var r2 := LongestGoodSubsequence("ABCABCABC", 4);
  expect r2 == 0, "impl test 2 failed";

  var r3 := LongestGoodSubsequence("A", 26);
  expect r3 == 0, "impl test 3 failed";

  var r4 := LongestGoodSubsequence("AAAAAAAAAAAAAAAAAAAAAA", 1);
  expect r4 == 22, "impl test 4 failed";

  var r5 := LongestGoodSubsequence("WEYYDIADTLCOUEG", 26);
  expect r5 == 0, "impl test 5 failed";

  var r6 := LongestGoodSubsequence("BA", 2);
  expect r6 == 2, "impl test 6 failed";

  var r7 := LongestGoodSubsequence("AABBCC", 3);
  expect r7 == 6, "impl test 7 failed";

  var r8 := LongestGoodSubsequence("A", 5);
  expect r8 == 0, "impl test 8 failed";

  var r9 := LongestGoodSubsequence("ABBBBBBBBB", 2);
  expect r9 == 2, "impl test 9 failed";

  var r10 := LongestGoodSubsequence("A", 1);
  expect r10 == 1, "impl test 10 failed";

  var r11 := LongestGoodSubsequence("ABBCCC", 3);
  expect r11 == 3, "impl test 11 failed";

  var r12 := LongestGoodSubsequence("AABBBBB", 2);
  expect r12 == 4, "impl test 12 failed";

  var r13 := LongestGoodSubsequence("ABCDEFGHIJKLMNOPQRSTUVWXYZABCDEFGHIJKLMNOPQRSTUVWXYABCDEFGHIJKLMNOPQRSTUVWXY", 26);
  expect r13 == 26, "impl test 13 failed";

  var r14 := LongestGoodSubsequence("AABBC", 3);
  expect r14 == 3, "impl test 14 failed";

  var r15 := LongestGoodSubsequence("AAC", 3);
  expect r15 == 0, "impl test 15 failed";

  var r16 := LongestGoodSubsequence("D", 4);
  expect r16 == 0, "impl test 16 failed";

  var r17 := LongestGoodSubsequence("BBB", 2);
  expect r17 == 0, "impl test 17 failed";

  var r18 := LongestGoodSubsequence("CBA", 3);
  expect r18 == 3, "impl test 18 failed";

  var r19 := LongestGoodSubsequence("ABC", 5);
  expect r19 == 0, "impl test 19 failed";

  print "All tests passed\n";
}