predicate IsPalindrome(t: string)
{
  forall i | 0 <= i < |t| / 2 :: t[i] == t[|t| - 1 - i]
}

function InsertCharAt(s: string, pos: nat): string
  requires pos <= |s|
{
  s[..pos] + "a" + s[pos..]
}

predicate DejaVuPost(s: string, possible: bool, result: string)
{
  (possible ==>
    (exists pos | 0 <= pos <= |s| :: result == InsertCharAt(s, pos))
    && !IsPalindrome(result))
  &&
  (!possible ==>
    forall pos | 0 <= pos <= |s| :: IsPalindrome(InsertCharAt(s, pos)))
}

method DejaVu(s: string) returns (possible: bool, result: string)
  ensures possible ==>
    (exists pos | 0 <= pos <= |s| :: result == InsertCharAt(s, pos))
    && !IsPalindrome(result)
  ensures !possible ==>
    forall pos | 0 <= pos <= |s| :: IsPalindrome(InsertCharAt(s, pos))
{
  var allA := true;
  var i := 0;
  while i < |s| && allA {
    if s[i] != 'a' {
      allA := false;
    }
    i := i + 1;
  }

  if allA {
    possible := false;
    result := "";
    return;
  }

  var sa := s + "a";
  var isPalin := true;
  var j := 0;
  while j < |sa| / 2 && isPalin {
    if sa[j] != sa[|sa| - 1 - j] {
      isPalin := false;
    }
    j := j + 1;
  }

  if isPalin {
    possible := true;
    result := "a" + s;
  } else {
    possible := true;
    result := s + "a";
  }
}

method Main()
{
  // === SPEC POSITIVE tests (small inputs, length 1-3) ===
  expect DejaVuPost("b", true, "ba"), "spec positive 1";
  expect DejaVuPost("ba", true, "baa"), "spec positive 2";
  expect DejaVuPost("ab", true, "aab"), "spec positive 3";
  expect DejaVuPost("a", false, ""), "spec positive 4";
  expect DejaVuPost("z", true, "za"), "spec positive 5";
  expect DejaVuPost("aa", false, ""), "spec positive 6";
  expect DejaVuPost("bb", true, "bba"), "spec positive 7";
  expect DejaVuPost("aaa", false, ""), "spec positive 8";
  expect DejaVuPost("aba", true, "abaa"), "spec positive 9";
  expect DejaVuPost("abc", true, "abca"), "spec positive 10";
  expect DejaVuPost("xy", true, "xya"), "spec positive 11";
  expect DejaVuPost("xx", true, "xxa"), "spec positive 12";
  expect DejaVuPost("mm", true, "mma"), "spec positive 13";
  expect DejaVuPost("cba", true, "cbaa"), "spec positive 14";
  expect DejaVuPost("aab", true, "aaba"), "spec positive 15";
  expect DejaVuPost("baa", true, "baaa"), "spec positive 16";
  expect DejaVuPost("xyx", true, "xyxa"), "spec positive 17";
  expect DejaVuPost("zza", true, "zzaa"), "spec positive 18";

  // === SPEC NEGATIVE tests (wrong outputs that spec should reject) ===
  // Neg 1: "ba" claimed impossible (but has non-'a' chars)
  expect !DejaVuPost("ba", false, ""), "spec negative 1";
  // Neg 2: "ab" with palindrome result "aba"
  expect !DejaVuPost("ab", true, "aba"), "spec negative 2";
  // Neg 3: "a" claimed possible with palindrome result "aa"
  expect !DejaVuPost("a", true, "aa"), "spec negative 3";
  // Neg 4: "z" with non-insertion result "zz"
  expect !DejaVuPost("z", true, "zz"), "spec negative 4";
  // Neg 5: "bb" with palindrome insertion "bab"
  expect !DejaVuPost("bb", true, "bab"), "spec negative 5";
  // Neg 6: "b" claimed impossible (but has non-'a' chars)
  expect !DejaVuPost("b", false, ""), "spec negative 6";
  // Neg 7: "xx" with palindrome insertion "xax"
  expect !DejaVuPost("xx", true, "xax"), "spec negative 7";
  // Neg 8: "aa" claimed possible with palindrome "aaa"
  expect !DejaVuPost("aa", true, "aaa"), "spec negative 8";
  // Neg 9: "xy" with non-insertion result "xyz"
  expect !DejaVuPost("xy", true, "xyz"), "spec negative 9";
  // Neg 10: "aaa" claimed possible with palindrome "aaaa"
  expect !DejaVuPost("aaa", true, "aaaa"), "spec negative 10";

  // === IMPLEMENTATION tests (full-size inputs) ===
  var p1, r1 := DejaVu("cbabc");
  expect p1 == true, "impl test 1a";
  expect r1 == "cbabca", "impl test 1b";

  var p2, r2 := DejaVu("ab");
  expect p2 == true, "impl test 2a";
  expect r2 == "aab", "impl test 2b";

  var p3, r3 := DejaVu("zza");
  expect p3 == true, "impl test 3a";
  expect r3 == "zzaa", "impl test 3b";

  var p4, r4 := DejaVu("ba");
  expect p4 == true, "impl test 4a";
  expect r4 == "baa", "impl test 4b";

  var p5, r5 := DejaVu("a");
  expect p5 == false, "impl test 5";

  var p6, r6 := DejaVu("nutforajaroftuna");
  expect p6 == true, "impl test 6a";
  expect r6 == "nutforajaroftunaa", "impl test 6b";

  var p7, r7 := DejaVu("aba");
  expect p7 == true, "impl test 7a";
  expect r7 == "abaa", "impl test 7b";

  var p8, r8 := DejaVu("aaa");
  expect p8 == false, "impl test 8";

  var p9, r9 := DejaVu("aaaa");
  expect p9 == false, "impl test 9";

  var p10, r10 := DejaVu("z");
  expect p10 == true, "impl test 10a";
  expect r10 == "za", "impl test 10b";

  var p11, r11 := DejaVu("b");
  expect p11 == true, "impl test 11a";
  expect r11 == "ba", "impl test 11b";

  var p12, r12 := DejaVu("bb");
  expect p12 == true, "impl test 12a";
  expect r12 == "bba", "impl test 12b";

  var p13, r13 := DejaVu("abc");
  expect p13 == true, "impl test 13a";
  expect r13 == "abca", "impl test 13b";

  var p14, r14 := DejaVu("cba");
  expect p14 == true, "impl test 14a";
  expect r14 == "cbaa", "impl test 14b";

  var p15, r15 := DejaVu("aab");
  expect p15 == true, "impl test 15a";
  expect r15 == "aaba", "impl test 15b";

  var p16, r16 := DejaVu("baa");
  expect p16 == true, "impl test 16a";
  expect r16 == "baaa", "impl test 16b";

  var p17, r17 := DejaVu("xx");
  expect p17 == true, "impl test 17a";
  expect r17 == "xxa", "impl test 17b";

  var p18, r18 := DejaVu("xyx");
  expect p18 == true, "impl test 18a";
  expect r18 == "xyxa", "impl test 18b";

  var p19, r19 := DejaVu("abcba");
  expect p19 == true, "impl test 19a";
  expect r19 == "abcbaa", "impl test 19b";

  var p20, r20 := DejaVu("aa");
  expect p20 == false, "impl test 20";

  var p21, r21 := DejaVu("racecar");
  expect p21 == true, "impl test 21a";
  expect r21 == "racecara", "impl test 21b";

  var p22, r22 := DejaVu("mm");
  expect p22 == true, "impl test 22a";
  expect r22 == "mma", "impl test 22b";

  var p23, r23 := DejaVu("xy");
  expect p23 == true, "impl test 23a";
  expect r23 == "xya", "impl test 23b";

  print "All tests passed\n";
}