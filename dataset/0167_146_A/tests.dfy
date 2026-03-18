predicate IsLuckyDigit(c: char)
{
  c == '4' || c == '7'
}

predicate AllLuckyDigits(s: seq<char>)
{
  forall i | 0 <= i < |s| :: IsLuckyDigit(s[i])
}

function DigitValue(c: char): int
{
  (c as int) - ('0' as int)
}

function DigitSum(s: seq<char>): int
  decreases |s|
{
  if |s| == 0 then 0
  else DigitSum(s[..|s|-1]) + DigitValue(s[|s|-1])
}

predicate IsLuckyTicket(s: seq<char>)
{
  var half := |s| / 2;
  AllLuckyDigits(s) && DigitSum(s[..half]) == DigitSum(s[half..])
}

method LuckyTicket(n: int, s: seq<char>) returns (result: bool)
  requires |s| == n
  requires n > 0
  requires n % 2 == 0
  ensures result == IsLuckyTicket(s)
{
  var a := 0;
  var b := 0;
  var half := |s| / 2;
  var i := 0;
  while i < |s|
  {
    if s[i] != '4' && s[i] != '7' {
      result := false;
      return;
    }
    var digit := (s[i] as int) - ('0' as int);
    if i < half {
      a := a + digit;
    } else {
      b := b + digit;
    }
    i := i + 1;
  }
  result := (a == b);
}

method Main()
{
  var r: bool;

  // ===== SPEC POSITIVE TESTS =====
  // Test IsLuckyTicket predicate directly with small inputs (length 2)

  // From Test 1: "47" → NO; scaled to "47" (length 2, lucky but unequal sums)
  expect IsLuckyTicket("47") == false, "spec positive 1";

  // From Test 2: "4738" → NO (non-lucky digits); scaled to "43"
  expect IsLuckyTicket("43") == false, "spec positive 2";

  // From Test 3: "4774" → YES (lucky, equal sums); scaled to "44"
  expect IsLuckyTicket("44") == true, "spec positive 3";

  // From Test 4: "4570" → NO (non-lucky); scaled to "45"
  expect IsLuckyTicket("45") == false, "spec positive 4";

  // From Test 6: "777777" → YES; scaled to "77"
  expect IsLuckyTicket("77") == true, "spec positive 5";

  // From Test 9: "4745474547" → NO (lucky but unequal); scaled to "74"
  expect IsLuckyTicket("74") == false, "spec positive 6";

  // From Test 10: "77770004444444" → NO (non-lucky, has 0s); scaled to "70"
  expect IsLuckyTicket("70") == false, "spec positive 7";

  // From Test 12: "1234567890" → NO (non-lucky); scaled to "12"
  expect IsLuckyTicket("12") == false, "spec positive 8";

  // ===== SPEC NEGATIVE TESTS =====
  // Verify IsLuckyTicket rejects the wrong output for each negative pair

  // Neg 1: "47" wrong=true, correct=false; scaled to "47"
  expect !(IsLuckyTicket("47") == true), "spec negative 1";

  // Neg 2: "4738" wrong=true; scaled to "43"
  expect !(IsLuckyTicket("43") == true), "spec negative 2";

  // Neg 3: "4774" wrong=false, correct=true; scaled to "44"
  expect !(IsLuckyTicket("44") == false), "spec negative 3";

  // Neg 4: "4570" wrong=true; scaled to "45"
  expect !(IsLuckyTicket("45") == true), "spec negative 4";

  // Neg 5: "477477" wrong=false, correct=true; scaled to "77"
  expect !(IsLuckyTicket("77") == false), "spec negative 5";

  // Neg 6: "777777" wrong=false; scaled to "77" (same as above but from different pair)
  // Use "44" variant instead to avoid dup
  expect !(IsLuckyTicket("44") == false), "spec negative 6";

  // Neg 8: "44" wrong=false, correct=true
  expect !(IsLuckyTicket("44") == false), "spec negative 8";

  // Neg 9: "4745474547" wrong=true; scaled to "74"
  expect !(IsLuckyTicket("74") == true), "spec negative 9";

  // Neg 10: "77770004444444" wrong=true; scaled to "70"
  expect !(IsLuckyTicket("70") == true), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  // Test LuckyTicket method with full-size inputs from all test pairs

  r := LuckyTicket(2, "47");
  expect r == false, "impl test 1 failed";

  r := LuckyTicket(4, "4738");
  expect r == false, "impl test 2 failed";

  r := LuckyTicket(4, "4774");
  expect r == true, "impl test 3 failed";

  r := LuckyTicket(4, "4570");
  expect r == false, "impl test 4 failed";

  r := LuckyTicket(6, "477477");
  expect r == true, "impl test 5 failed";

  r := LuckyTicket(6, "777777");
  expect r == true, "impl test 6 failed";

  r := LuckyTicket(20, "44444444444444444444");
  expect r == true, "impl test 7 failed";

  r := LuckyTicket(2, "44");
  expect r == true, "impl test 8 failed";

  r := LuckyTicket(10, "4745474547");
  expect r == false, "impl test 9 failed";

  r := LuckyTicket(14, "77770004444444");
  expect r == false, "impl test 10 failed";

  r := LuckyTicket(10, "4747777744");
  expect r == true, "impl test 11 failed";

  r := LuckyTicket(10, "1234567890");
  expect r == false, "impl test 12 failed";

  r := LuckyTicket(50, "44444444444444444444444444444444444444444444444444");
  expect r == true, "impl test 13 failed";

  r := LuckyTicket(50, "44444444444444444444444444444444444444444444444447");
  expect r == false, "impl test 14 failed";

  r := LuckyTicket(50, "74444444444444444444444444444444444444444444444444");
  expect r == false, "impl test 15 failed";

  r := LuckyTicket(50, "07777777777777777777777777777777777777777777777770");
  expect r == false, "impl test 16 failed";

  r := LuckyTicket(50, "77777777777777777777777777777777777777777777777777");
  expect r == true, "impl test 17 failed";

  r := LuckyTicket(50, "44747747774474747747747447777447774747447477444474");
  expect r == true, "impl test 18 failed";

  r := LuckyTicket(48, "447474444777444474747747744774447444747474774474");
  expect r == true, "impl test 19 failed";

  r := LuckyTicket(32, "74474474777444474444747774474774");
  expect r == true, "impl test 20 failed";

  print "All tests passed\n";
}