method JugglingLetters(n: int, strings: seq<string>) returns (result: bool)
{
  var allChars: seq<char> := [];
  var i := 0;
  while i < |strings| {
    var j := 0;
    while j < |strings[i]| {
      allChars := allChars + [strings[i][j]];
      j := j + 1;
    }
    i := i + 1;
  }

  result := true;
  i := 0;
  while i < |allChars| {
    var count := 0;
    var j := 0;
    while j < |allChars| {
      if allChars[j] == allChars[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    if count % n != 0 {
      result := false;
      return;
    }
    i := i + 1;
  }
}

method Main()
{
  // Test 1, case 1: n=2, ["caa", "cbb"] → YES
  var r1 := JugglingLetters(2, ["caa", "cbb"]);
  expect r1 == true, "Test 1.1 failed";

  // Test 1, case 2: n=3, ["cba", "cba", "cbb"] → NO
  var r2 := JugglingLetters(3, ["cba", "cba", "cbb"]);
  expect r2 == false, "Test 1.2 failed";

  // Test 1, case 3: n=4, ["ccab", "cbac", "bca", "acbcc"] → YES
  var r3 := JugglingLetters(4, ["ccab", "cbac", "bca", "acbcc"]);
  expect r3 == true, "Test 1.3 failed";

  // Test 1, case 4: n=4, ["acb", "caf", "c", "cbafc"] → NO
  var r4 := JugglingLetters(4, ["acb", "caf", "c", "cbafc"]);
  expect r4 == false, "Test 1.4 failed";

  // Test 2: n=3, ["cca", "cca", "caa"] → NO
  var r5 := JugglingLetters(3, ["cca", "cca", "caa"]);
  expect r5 == false, "Test 2 failed";

  // Test 3: n=3, ["abca", "abc", "bca"] → NO
  var r6 := JugglingLetters(3, ["abca", "abc", "bca"]);
  expect r6 == false, "Test 3 failed";

  // Test 4: n=2, ["aab", "abb"] → NO
  var r7 := JugglingLetters(2, ["aab", "abb"]);
  expect r7 == false, "Test 4 failed";

  // Test 5: n=3, ["caac", "cbbb", "aaac"] → NO
  var r8 := JugglingLetters(3, ["caac", "cbbb", "aaac"]);
  expect r8 == false, "Test 5 failed";

  // Test 6: n=2, ["aaaaaaa", "aaaaaa"] → NO
  var r9 := JugglingLetters(2, ["aaaaaaa", "aaaaaa"]);
  expect r9 == false, "Test 6 failed";

  // Test 7: n=2, ["xx", "z"] → NO
  var r10 := JugglingLetters(2, ["xx", "z"]);
  expect r10 == false, "Test 7 failed";

  // Test 8: n=3, ["abc", "abc", "abcdddd"] → NO
  var r11 := JugglingLetters(3, ["abc", "abc", "abcdddd"]);
  expect r11 == false, "Test 8 failed";

  // Test 9: n=2, ["aa", "bbb"] → NO
  var r12 := JugglingLetters(2, ["aa", "bbb"]);
  expect r12 == false, "Test 9 failed";

  // Test 10: n=3, ["a", "aa", "aaaa"] → NO
  var r13 := JugglingLetters(3, ["a", "aa", "aaaa"]);
  expect r13 == false, "Test 10 failed";

  // Test 11: n=2, ["abc", "adc"] → NO
  var r14 := JugglingLetters(2, ["abc", "adc"]);
  expect r14 == false, "Test 11 failed";

  // Test 12: n=2, ["zzz", "zzzz"] → NO
  var r15 := JugglingLetters(2, ["zzz", "zzzz"]);
  expect r15 == false, "Test 12 failed";

  // Test 13: n=2, ["aa", "b"] → NO
  var r16 := JugglingLetters(2, ["aa", "b"]);
  expect r16 == false, "Test 13 failed";

  // Test 14: n=2, ["aa", "aaa"] → NO
  var r17 := JugglingLetters(2, ["aa", "aaa"]);
  expect r17 == false, "Test 14 failed";

  // Test 15: n=2, ["z", "y"] → NO
  var r18 := JugglingLetters(2, ["z", "y"]);
  expect r18 == false, "Test 15 failed";

  // Test 16: n=3, ["aaa", "abb", "abb"] → NO
  var r19 := JugglingLetters(3, ["aaa", "abb", "abb"]);
  expect r19 == false, "Test 16 failed";

  // Test 17: n=3, ["adddd", "a", "a"] → NO
  var r20 := JugglingLetters(3, ["adddd", "a", "a"]);
  expect r20 == false, "Test 17 failed";

  // Test 18: n=2, ["aaab", "aaabb"] → NO
  var r21 := JugglingLetters(2, ["aaab", "aaabb"]);
  expect r21 == false, "Test 18 failed";

  // Test 19: n=2, ["aaa", "bbb"] → NO
  var r22 := JugglingLetters(2, ["aaa", "bbb"]);
  expect r22 == false, "Test 19 failed";

  // Test 20: n=2, ["aa", "a"] → NO
  var r23 := JugglingLetters(2, ["aa", "a"]);
  expect r23 == false, "Test 20 failed";

  print "All tests passed\n";
}