predicate AllLowercase(s: string)
{
  forall i | 0 <= i < |s| :: 'a' <= s[i] <= 'z'
}

predicate AllDistinct(s: string)
{
  forall i, j | 0 <= i < |s| && 0 <= j < |s| && i != j :: s[i] != s[j]
}

function MinCharVal(s: string): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0] as int
  else
    var rest := MinCharVal(s[..|s|-1]);
    var last := s[|s|-1] as int;
    if last < rest then last else rest
}

function MaxCharVal(s: string): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0] as int
  else
    var rest := MaxCharVal(s[..|s|-1]);
    var last := s[|s|-1] as int;
    if last > rest then last else rest
}

predicate IsDiverse(s: string)
{
  AllLowercase(s) &&
  AllDistinct(s) &&
  (|s| == 0 || MaxCharVal(s) - MinCharVal(s) + 1 == |s|)
}

method DiverseStrings(strings: seq<string>) returns (results: seq<bool>)
  requires forall i | 0 <= i < |strings| :: AllLowercase(strings[i])
  ensures |results| == |strings|
  ensures forall i | 0 <= i < |strings| :: results[i] == IsDiverse(strings[i])
{
  results := [];
  var idx := 0;
  while idx < |strings|
  {
    var a := strings[idx];
    var b := new int[26];
    var j := 0;
    while j < 26
    {
      b[j] := 0;
      j := j + 1;
    }
    j := 0;
    while j < |a|
    {
      var c := a[j] as int - 97;
      if 0 <= c < 26 {
        b[c] := b[c] + 1;
      }
      j := j + 1;
    }
    var diverse := true;
    var y := 0;
    var x := 0;
    var k := 0;
    while k < 27
    {
      var val := if k < 26 then b[k] else 0;
      if val > 1 {
        diverse := false;
        break;
      }
      if y == 0 && val == 1 {
        y := 1;
      }
      if y == 1 && val == 0 {
        x := 1;
        y := 0;
      }
      if x == 1 && val >= 1 {
        diverse := false;
        break;
      }
      k := k + 1;
    }
    results := results + [diverse];
    idx := idx + 1;
  }
}

method Main()
{
  // ========== SPEC POSITIVE TESTS ==========
  // Testing IsDiverse (the top-level ensures predicate) with correct expected values

  // From Test 1
  expect IsDiverse("r") == true, "spec positive 1";
  expect IsDiverse("aa") == false, "spec positive 2";
  expect IsDiverse("az") == false, "spec positive 3";
  expect IsDiverse("bad") == false, "spec positive 4";

  // From Test 2
  expect IsDiverse("no") == true, "spec positive 5";
  expect IsDiverse("bc") == true, "spec positive 6";
  expect IsDiverse("cb") == true, "spec positive 7";
  expect IsDiverse("z") == true, "spec positive 8";
  expect IsDiverse("a") == true, "spec positive 9";
  expect IsDiverse("qq") == false, "spec positive 10";
  expect IsDiverse("op") == true, "spec positive 11";
  expect IsDiverse("ab") == true, "spec positive 12";
  expect IsDiverse("abc") == true, "spec positive 13";
  expect IsDiverse("ac") == false, "spec positive 14";
  expect IsDiverse("ops") == false, "spec positive 15";
  expect IsDiverse("yes") == false, "spec positive 16";
  expect IsDiverse("xy") == true, "spec positive 17";
  expect IsDiverse("yx") == true, "spec positive 18";
  expect IsDiverse("po") == true, "spec positive 19";

  // From Test 3
  expect IsDiverse("f") == true, "spec positive 20";

  // From Test 10
  expect IsDiverse("sho") == false, "spec positive 21";

  // From Test 11
  expect IsDiverse("shh") == false, "spec positive 22";

  // From Test 14
  expect IsDiverse("soo") == false, "spec positive 23";

  // ========== SPEC NEGATIVE TESTS ==========
  // Testing that IsDiverse rejects wrong outputs from negative test pairs

  // Neg 3: "f" correct=true, wrong=false
  expect !(IsDiverse("f") == false), "spec negative 1";

  // Neg 10: "sho" correct=false, wrong=true
  expect !(IsDiverse("sho") == true), "spec negative 2";

  // Neg 9: "shoh" correct=false, wrong=true
  expect !(IsDiverse("shoh") == true), "spec negative 3";

  // Neg 8: "shohr" correct=false, wrong=true
  expect !(IsDiverse("shohr") == true), "spec negative 4";

  // Neg 7: "shohru" correct=false, wrong=true
  expect !(IsDiverse("shohru") == true), "spec negative 5";

  // Neg 6: "shohruk" correct=false, wrong=true
  expect !(IsDiverse("shohruk") == true), "spec negative 6";

  // Neg 4: "shohrukh" correct=false, wrong=true
  expect !(IsDiverse("shohrukh") == true), "spec negative 7";

  // ========== IMPLEMENTATION TESTS ==========

  // Test 1
  var r1 := DiverseStrings(["fced", "xyz", "r", "dabcef", "az", "aa", "bad", "babc"]);
  expect r1 == [true, true, true, true, false, false, false, false], "impl test 1 failed";

  // Test 2
  var r2 := DiverseStrings([
    "ops", "test", "yes", "no", "ac", "bc", "cb", "z", "a", "q",
    "r", "u", "qq", "op", "po", "xu", "ux", "xy", "yx", "a",
    "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "bcdefg", "cdefg", "defg", "efgd",
    "efef", "abacaba", "abz", "aoi", "ioi", "codeforces", "klmn", "nmlk", "kln", "klmnl",
    "kmn", "kklmn", "klmnn", "aklkmn"
  ]);
  expect r2 == [
    false, false, false, true, false, true, true, true, true, true,
    true, true, false, true, true, false, false, true, true, true,
    true, true, true, true, true, true, true, true, true, true,
    false, false, false, false, false, false, true, true, false, false,
    false, false, false, false
  ], "impl test 2 failed";

  // Test 3
  var r3 := DiverseStrings(["f"]);
  expect r3 == [true], "impl test 3 failed";

  // Test 4
  var r4 := DiverseStrings(["shohrukh"]);
  expect r4 == [false], "impl test 4 failed";

  // Test 5: 69 copies of "abc", all true
  var input5: seq<string> := [];
  var expected5: seq<bool> := [];
  var i := 0;
  while i < 69
  {
    input5 := input5 + ["abc"];
    expected5 := expected5 + [true];
    i := i + 1;
  }
  var r5 := DiverseStrings(input5);
  expect r5 == expected5, "impl test 5 failed";

  // Test 6
  var r6 := DiverseStrings(["shohruk"]);
  expect r6 == [false], "impl test 6 failed";

  // Test 7
  var r7 := DiverseStrings(["shohru"]);
  expect r7 == [false], "impl test 7 failed";

  // Test 8
  var r8 := DiverseStrings(["shohr"]);
  expect r8 == [false], "impl test 8 failed";

  // Test 9
  var r9 := DiverseStrings(["shoh"]);
  expect r9 == [false], "impl test 9 failed";

  // Test 10
  var r10 := DiverseStrings(["sho"]);
  expect r10 == [false], "impl test 10 failed";

  // Test 11
  var r11 := DiverseStrings(["shh"]);
  expect r11 == [false], "impl test 11 failed";

  // Test 12
  var r12 := DiverseStrings(["shhh"]);
  expect r12 == [false], "impl test 12 failed";

  // Test 13
  var r13 := DiverseStrings(["shhhh"]);
  expect r13 == [false], "impl test 13 failed";

  // Test 14
  var r14 := DiverseStrings(["soo"]);
  expect r14 == [false], "impl test 14 failed";

  // Test 15
  var r15 := DiverseStrings(["aadde"]);
  expect r15 == [false], "impl test 15 failed";

  // Test 16
  var r16 := DiverseStrings(["sooo"]);
  expect r16 == [false], "impl test 16 failed";

  // Test 17
  var r17 := DiverseStrings(["sdfalusdbfja"]);
  expect r17 == [false], "impl test 17 failed";

  // Test 18
  var r18 := DiverseStrings(["abcxyz"]);
  expect r18 == [false], "impl test 18 failed";

  // Test 19
  var r19 := DiverseStrings(["aaaab"]);
  expect r19 == [false], "impl test 19 failed";

  // Test 20
  var r20 := DiverseStrings(["bcef"]);
  expect r20 == [false], "impl test 20 failed";

  print "All tests passed\n";
}