predicate IsDigitChar(c: char)
{
  '0' <= c <= '9'
}

predicate AllDigits(s: string)
{
  forall i | 0 <= i < |s| :: IsDigitChar(s[i])
}

function DigitVal(c: char): int
  requires IsDigitChar(c)
{
  (c as int) - ('0' as int)
}

function StringToNat(s: string): int
  requires |s| > 0
  requires AllDigits(s)
  decreases |s|
{
  if |s| == 1 then DigitVal(s[0])
  else StringToNat(s[..|s|-1]) * 10 + DigitVal(s[|s|-1])
}

function CountEvenEndingHere(s: string): int
  requires |s| > 0
  requires AllDigits(s)
  decreases |s|
{
  var thisOne := if StringToNat(s) % 2 == 0 then 1 else 0;
  if |s| == 1 then thisOne
  else thisOne + CountEvenEndingHere(s[1..])
}

function CountEvenSubstrings(s: string): int
  requires AllDigits(s)
  decreases |s|
{
  if |s| == 0 then 0
  else CountEvenSubstrings(s[..|s|-1]) + CountEvenEndingHere(s)
}

method EvenSubstrings(s: string) returns (count: int)
  requires AllDigits(s)
  ensures count == CountEvenSubstrings(s)
{
  count := 0;
  for i := 0 to |s| {
    if s[i] == '0' || s[i] == '2' || s[i] == '4' || s[i] == '6' || s[i] == '8' {
      count := count + i + 1;
    }
  }
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // ensures: count == CountEvenSubstrings(s)
  // Testing that CountEvenSubstrings(s) == correct_output for small inputs

  expect CountEvenSubstrings("1234") == 6, "spec positive 1";
  expect CountEvenSubstrings("2244") == 10, "spec positive 2";
  expect CountEvenSubstrings("3") == 0, "spec positive 3";
  expect CountEvenSubstrings("6") == 1, "spec positive 4";
  // Test 5 skipped (length 10, too expensive for recursive spec)
  expect CountEvenSubstrings("13") == 0, "spec positive 6";
  expect CountEvenSubstrings("18") == 2, "spec positive 7";
  expect CountEvenSubstrings("81") == 1, "spec positive 8";
  expect CountEvenSubstrings("68") == 3, "spec positive 9";
  expect CountEvenSubstrings("111") == 0, "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // Testing that CountEvenSubstrings(s) != wrong_output for small inputs

  expect CountEvenSubstrings("1234") != 7, "spec negative 1";
  expect CountEvenSubstrings("2244") != 11, "spec negative 2";
  expect CountEvenSubstrings("3") != 1, "spec negative 3";
  expect CountEvenSubstrings("6") != 2, "spec negative 4";
  // Test 5 skipped (length 10, too expensive for recursive spec)
  expect CountEvenSubstrings("13") != 1, "spec negative 6";
  expect CountEvenSubstrings("18") != 3, "spec negative 7";
  expect CountEvenSubstrings("81") != 2, "spec negative 8";
  expect CountEvenSubstrings("68") != 4, "spec negative 9";
  expect CountEvenSubstrings("111") != 1, "spec negative 10";

  // === IMPLEMENTATION TESTS ===

  var r1 := EvenSubstrings("1234");
  expect r1 == 6, "impl test 1 failed";

  var r2 := EvenSubstrings("2244");
  expect r2 == 10, "impl test 2 failed";

  var r3 := EvenSubstrings("3");
  expect r3 == 0, "impl test 3 failed";

  var r4 := EvenSubstrings("6");
  expect r4 == 1, "impl test 4 failed";

  var r5 := EvenSubstrings("9572683145");
  expect r5 == 24, "impl test 5 failed";

  var r6 := EvenSubstrings("13");
  expect r6 == 0, "impl test 6 failed";

  var r7 := EvenSubstrings("18");
  expect r7 == 2, "impl test 7 failed";

  var r8 := EvenSubstrings("81");
  expect r8 == 1, "impl test 8 failed";

  var r9 := EvenSubstrings("68");
  expect r9 == 3, "impl test 9 failed";

  var r10 := EvenSubstrings("111");
  expect r10 == 0, "impl test 10 failed";

  var r11 := EvenSubstrings("112");
  expect r11 == 3, "impl test 11 failed";

  var r12 := EvenSubstrings("121");
  expect r12 == 2, "impl test 12 failed";

  var r13 := EvenSubstrings("122");
  expect r13 == 5, "impl test 13 failed";

  var r14 := EvenSubstrings("211");
  expect r14 == 1, "impl test 14 failed";

  var r15 := EvenSubstrings("212");
  expect r15 == 4, "impl test 15 failed";

  var r16 := EvenSubstrings("221");
  expect r16 == 3, "impl test 16 failed";

  var r17 := EvenSubstrings("222");
  expect r17 == 6, "impl test 17 failed";

  var r18 := EvenSubstrings("263254663359864483324578786753512345165");
  expect r18 == 327, "impl test 18 failed";

  print "All tests passed\n";
}