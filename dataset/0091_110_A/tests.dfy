// --- Specification ---

function Abs(n: int): nat {
  if n < 0 then -n else n
}

predicate IsLuckyDigit(d: int) {
  d == 4 || d == 7
}

function Digits(n: nat): seq<int>
  decreases n
{
  if n == 0 then []
  else Digits(n / 10) + [n % 10]
}

function CountLucky(s: seq<int>): nat
  decreases |s|
{
  if |s| == 0 then 0
  else CountLucky(s[..|s|-1]) + (if IsLuckyDigit(s[|s|-1]) then 1 else 0)
}

predicate IsLuckyNumber(n: nat) {
  var d := Digits(n);
  n > 0 && forall i | 0 <= i < |d| :: IsLuckyDigit(d[i])
}

predicate IsNearlyLucky(n: int) {
  IsLuckyNumber(CountLucky(Digits(Abs(n))))
}

// --- Implementation ---

method NearlyLucky(n: int) returns (result: bool)
  ensures result == IsNearlyLucky(n)
{
  var num := if n < 0 then -n else n;
  if num == 0 {
    result := false;
    return;
  }
  var count := 0;
  var temp := num;
  while temp > 0 {
    var digit := temp % 10;
    if digit == 4 || digit == 7 {
      count := count + 1;
    }
    temp := temp / 10;
  }
  if count == 0 {
    result := false;
    return;
  }
  var flag := true;
  temp := count;
  while temp > 0 {
    var digit := temp % 10;
    if digit != 4 && digit != 7 {
      flag := false;
    }
    temp := temp / 10;
  }
  result := flag;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // For each positive test pair, verify IsNearlyLucky(input) == correct_output.
  // Large inputs are scaled down to small equivalents.

  expect IsNearlyLucky(40047) == false, "spec positive 1";        // 3 lucky digits -> not lucky number
  expect IsNearlyLucky(7747774) == true, "spec positive 2";       // 7 lucky digits -> 7 is lucky number
  expect IsNearlyLucky(100) == false, "spec positive 3";          // scaled from 10^18; 0 lucky digits
  expect IsNearlyLucky(7) == false, "spec positive 4";            // 1 lucky digit -> 1 not lucky number
  expect IsNearlyLucky(4) == false, "spec positive 5";            // 1 lucky digit -> 1 not lucky number
  expect IsNearlyLucky(474404774) == false, "spec positive 6";    // 8 lucky digits -> 8 not lucky number
  expect IsNearlyLucky(4444) == true, "spec positive 7";          // scaled from 4744000695826; 4 lucky digits -> 4 is lucky number
  expect IsNearlyLucky(4747474) == true, "spec positive 8";       // scaled from 10000000004744744; 7 lucky digits -> 7 is lucky number
  expect IsNearlyLucky(4444444) == true, "spec positive 9";       // scaled from 446486416781684178; 7 lucky digits -> 7 is lucky number
  expect IsNearlyLucky(999999999) == false, "spec positive 10";   // 0 lucky digits

  // === SPEC NEGATIVE TESTS ===
  // For each negative test pair, verify IsNearlyLucky(input) != wrong_output.

  expect IsNearlyLucky(40047) != true, "spec negative 1";         // wrong claims YES, correct is NO
  expect IsNearlyLucky(7747774) != false, "spec negative 2";      // wrong claims NO, correct is YES
  expect IsNearlyLucky(100) != true, "spec negative 3";           // scaled from 10^18; wrong claims YES
  expect IsNearlyLucky(7) != true, "spec negative 4";             // wrong claims YES, correct is NO
  expect IsNearlyLucky(4) != true, "spec negative 5";             // wrong claims YES, correct is NO
  expect IsNearlyLucky(474404774) != true, "spec negative 6";     // wrong claims YES, correct is NO
  expect IsNearlyLucky(4444) != false, "spec negative 7";         // scaled from 4744000695826; wrong claims NO
  expect IsNearlyLucky(4747474) != false, "spec negative 8";      // scaled from 10000000004744744; wrong claims NO
  expect IsNearlyLucky(4444444) != false, "spec negative 9";      // scaled from 446486416781684178; wrong claims NO
  expect IsNearlyLucky(999999999) != true, "spec negative 10";    // wrong claims YES, correct is NO

  // === IMPLEMENTATION TESTS ===
  // Call the method with full-size inputs and check correct output.

  var r1 := NearlyLucky(40047);
  expect r1 == false, "impl test 1 failed";

  var r2 := NearlyLucky(7747774);
  expect r2 == true, "impl test 2 failed";

  var r3 := NearlyLucky(1000000000000000000);
  expect r3 == false, "impl test 3 failed";

  var r4 := NearlyLucky(7);
  expect r4 == false, "impl test 4 failed";

  var r5 := NearlyLucky(4);
  expect r5 == false, "impl test 5 failed";

  var r6 := NearlyLucky(474404774);
  expect r6 == false, "impl test 6 failed";

  var r7 := NearlyLucky(4744000695826);
  expect r7 == true, "impl test 7 failed";

  var r8 := NearlyLucky(10000000004744744);
  expect r8 == true, "impl test 8 failed";

  var r9 := NearlyLucky(446486416781684178);
  expect r9 == true, "impl test 9 failed";

  var r10 := NearlyLucky(999999999);
  expect r10 == false, "impl test 10 failed";

  var r11 := NearlyLucky(7777);
  expect r11 == true, "impl test 11 failed";

  var r12 := NearlyLucky(87414417444);
  expect r12 == false, "impl test 12 failed";

  var r13 := NearlyLucky(111222333444555667);
  expect r13 == true, "impl test 13 failed";

  var r14 := NearlyLucky(1);
  expect r14 == false, "impl test 14 failed";

  var r15 := NearlyLucky(4700);
  expect r15 == false, "impl test 15 failed";

  var r16 := NearlyLucky(3794555488744477);
  expect r16 == false, "impl test 16 failed";

  var r17 := NearlyLucky(444444444444444444);
  expect r17 == false, "impl test 17 failed";

  var r18 := NearlyLucky(474447447774444774);
  expect r18 == false, "impl test 18 failed";

  var r19 := NearlyLucky(777777777777777);
  expect r19 == false, "impl test 19 failed";

  var r20 := NearlyLucky(34777745021000000);
  expect r20 == false, "impl test 20 failed";

  print "All tests passed\n";
}