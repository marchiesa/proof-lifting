function RemoveAt(s: string, idx: nat): string
  requires idx < |s|
{
  s[..idx] + s[idx + 1..]
}

function InsertAt(s: string, idx: nat, c: char): string
  requires idx <= |s|
{
  s[..idx] + [c] + s[idx..]
}

function TotalLength(strings: seq<string>): nat
  decreases |strings|
{
  if |strings| == 0 then 0
  else TotalLength(strings[..|strings| - 1]) + |strings[|strings| - 1]|
}

predicate AllEqual(strings: seq<string>)
{
  forall i | 0 <= i < |strings| :: forall j | 0 <= j < |strings| :: strings[i] == strings[j]
}

predicate CanReachAllEqual(state: seq<string>, steps: nat)
  decreases steps
{
  AllEqual(state) ||
  (steps > 0 &&
   exists si | 0 <= si < |state| ::
     exists sp | 0 <= sp < |state[si]| ::
       exists di | 0 <= di < |state| ::
         var ch := state[si][sp];
         var afterRemove := state[si := RemoveAt(state[si], sp)];
         exists dp | 0 <= dp <= |afterRemove[di]| ::
           CanReachAllEqual(afterRemove[di := InsertAt(afterRemove[di], dp, ch)], steps - 1))
}

method JugglingLetters(n: int, strings: seq<string>) returns (result: bool)
  requires n > 0
  requires n == |strings|
  ensures result == CanReachAllEqual(strings, TotalLength(strings))
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
  // === SPEC POSITIVE TESTS ===
  // Test: CanReachAllEqual(strings, TotalLength(strings)) == correct_output
  // Small inputs only to keep bounded quantifier evaluation feasible.

  // Scaled from Test 1.1 (n=2, YES): already-equal single-char strings
  expect CanReachAllEqual(["a", "a"], TotalLength(["a", "a"])) == true, "spec positive 1";

  // Scaled from Test 1.2 (n=3, NO): char count 1 not divisible by 3
  expect CanReachAllEqual(["a", "", ""], TotalLength(["a", "", ""])) == false, "spec positive 2";

  // Scaled from Test 1.3 (n=4, YES): trivially equal 4 strings
  expect CanReachAllEqual(["a", "a", "a", "a"], TotalLength(["a", "a", "a", "a"])) == true, "spec positive 3";

  // Scaled from Test 1.4 (n=2, NO): distinct chars, each count 1 not div 2
  expect CanReachAllEqual(["a", "b"], TotalLength(["a", "b"])) == false, "spec positive 4";

  // Scaled from Test 2 (n=3, NO): single char among 3 strings
  expect CanReachAllEqual(["", "a", ""], TotalLength(["", "a", ""])) == false, "spec positive 5";

  // Scaled from Test 4 (n=2, NO): one char, count 1 not div 2
  expect CanReachAllEqual(["a", ""], TotalLength(["a", ""])) == false, "spec positive 6";

  // Scaled from Test 7 (n=2, NO): single different char
  expect CanReachAllEqual(["", "b"], TotalLength(["", "b"])) == false, "spec positive 7";

  // Non-trivial true case (n=2, YES): chars redistributable, each count div 2
  expect CanReachAllEqual(["ab", "ba"], TotalLength(["ab", "ba"])) == true, "spec positive 8";

  // === SPEC NEGATIVE TESTS ===
  // Wrong output claims true, but correct is false.
  // Test: CanReachAllEqual(strings, TotalLength(strings)) != true
  // (Negative 1 skipped: wrong output differs only in formatting, not boolean value)

  // Scaled from Negative 2 (n=3, wrong=true, correct=false)
  expect CanReachAllEqual(["a", "", ""], TotalLength(["a", "", ""])) != true, "spec negative 2";

  // Scaled from Negative 3 (n=3, wrong=true, correct=false)
  expect CanReachAllEqual(["a", "b", ""], TotalLength(["a", "b", ""])) != true, "spec negative 3";

  // Scaled from Negative 4 (n=2, wrong=true, correct=false)
  expect CanReachAllEqual(["a", "b"], TotalLength(["a", "b"])) != true, "spec negative 4";

  // Scaled from Negative 5 (n=3, wrong=true, correct=false)
  expect CanReachAllEqual(["a", "a", ""], TotalLength(["a", "a", ""])) != true, "spec negative 5";

  // Scaled from Negative 6 (n=2, wrong=true, correct=false)
  expect CanReachAllEqual(["a", ""], TotalLength(["a", ""])) != true, "spec negative 6";

  // Scaled from Negative 7 (n=2, wrong=true, correct=false)
  expect CanReachAllEqual(["", "b"], TotalLength(["", "b"])) != true, "spec negative 7";

  // Scaled from Negative 8 (n=3, wrong=true, correct=false)
  expect CanReachAllEqual(["", "", "b"], TotalLength(["", "", "b"])) != true, "spec negative 8";

  // Scaled from Negative 9 (n=2, wrong=true, correct=false)
  expect CanReachAllEqual(["ab", ""], TotalLength(["ab", ""])) != true, "spec negative 9";

  // Scaled from Negative 10 (n=3, wrong=true, correct=false)
  expect CanReachAllEqual(["b", "", ""], TotalLength(["b", "", ""])) != true, "spec negative 10";

  // === IMPLEMENTATION TESTS ===
  var r1 := JugglingLetters(2, ["caa", "cbb"]);
  expect r1 == true, "impl test 1 failed";

  var r2 := JugglingLetters(3, ["cba", "cba", "cbb"]);
  expect r2 == false, "impl test 2 failed";

  var r3 := JugglingLetters(4, ["ccab", "cbac", "bca", "acbcc"]);
  expect r3 == true, "impl test 3 failed";

  var r4 := JugglingLetters(4, ["acb", "caf", "c", "cbafc"]);
  expect r4 == false, "impl test 4 failed";

  var r5 := JugglingLetters(3, ["cca", "cca", "caa"]);
  expect r5 == false, "impl test 5 failed";

  var r6 := JugglingLetters(3, ["abca", "abc", "bca"]);
  expect r6 == false, "impl test 6 failed";

  var r7 := JugglingLetters(2, ["aab", "abb"]);
  expect r7 == false, "impl test 7 failed";

  var r8 := JugglingLetters(3, ["caac", "cbbb", "aaac"]);
  expect r8 == false, "impl test 8 failed";

  var r9 := JugglingLetters(2, ["aaaaaaa", "aaaaaa"]);
  expect r9 == false, "impl test 9 failed";

  var r10 := JugglingLetters(2, ["xx", "z"]);
  expect r10 == false, "impl test 10 failed";

  var r11 := JugglingLetters(3, ["abc", "abc", "abcdddd"]);
  expect r11 == false, "impl test 11 failed";

  var r12 := JugglingLetters(2, ["aa", "bbb"]);
  expect r12 == false, "impl test 12 failed";

  var r13 := JugglingLetters(3, ["a", "aa", "aaaa"]);
  expect r13 == false, "impl test 13 failed";

  var r14 := JugglingLetters(2, ["abc", "adc"]);
  expect r14 == false, "impl test 14 failed";

  var r15 := JugglingLetters(2, ["zzz", "zzzz"]);
  expect r15 == false, "impl test 15 failed";

  var r16 := JugglingLetters(2, ["aa", "b"]);
  expect r16 == false, "impl test 16 failed";

  var r17 := JugglingLetters(2, ["aa", "aaa"]);
  expect r17 == false, "impl test 17 failed";

  var r18 := JugglingLetters(2, ["z", "y"]);
  expect r18 == false, "impl test 18 failed";

  var r19 := JugglingLetters(3, ["aaa", "abb", "abb"]);
  expect r19 == false, "impl test 19 failed";

  var r20 := JugglingLetters(3, ["adddd", "a", "a"]);
  expect r20 == false, "impl test 20 failed";

  var r21 := JugglingLetters(2, ["aaab", "aaabb"]);
  expect r21 == false, "impl test 21 failed";

  var r22 := JugglingLetters(2, ["aaa", "bbb"]);
  expect r22 == false, "impl test 22 failed";

  var r23 := JugglingLetters(2, ["aa", "a"]);
  expect r23 == false, "impl test 23 failed";

  print "All tests passed\n";
}