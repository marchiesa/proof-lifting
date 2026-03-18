// ===== Specification =====

function Abs(n: int): nat
{
  if n >= 0 then n else -n
}

function DigitSum(n: int): nat
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else (n % 10) + DigitSum(n / 10)
}

function MaxCommonDivisor(a: int, b: int, candidate: int): nat
  requires a >= 0 && b >= 0 && candidate >= 0
  decreases candidate
{
  if candidate == 0 then 0
  else if a % candidate == 0 && b % candidate == 0 then candidate
  else MaxCommonDivisor(a, b, candidate - 1)
}

function GcdSpec(a: int, b: int): nat
  requires a >= 0 && b >= 0
{
  if a == 0 && b == 0 then 0
  else MaxCommonDivisor(a, b, a + b)
}

function GcdSumOf(x: int): nat
  requires x >= 0
{
  GcdSpec(x, DigitSum(x))
}

// Combined predicate for all three ensures clauses of GcdSum
predicate GcdSumMeetsSpec(n: int, x: int)
  requires n >= 1
  requires x >= 0
{
  x >= n && GcdSumOf(x) > 1 && (forall y | n <= y < x :: GcdSumOf(y) <= 1)
}

// ===== Implementation =====

method Gcd(a: int, b: int) returns (g: int)
  ensures g == GcdSpec(Abs(a), Abs(b))
  decreases *
{
  var x := a;
  var y := b;
  if x < 0 { x := -x; }
  if y < 0 { y := -y; }
  while y != 0
    decreases *
  {
    var temp := y;
    y := x % y;
    x := temp;
  }
  g := x;
}

method GcdSum(n: int) returns (x: int)
  requires n >= 1
  ensures x >= n
  ensures GcdSumOf(x) > 1
  ensures forall y | n <= y < x :: GcdSumOf(y) <= 1
  decreases *
{
  x := n;
  while true
    decreases *
  {
    var digitSum := 0;
    var temp := x;
    if temp < 0 { temp := -temp; }
    while temp > 0
      decreases *
    {
      digitSum := digitSum + (temp % 10);
      temp := temp / 10;
    }
    var g := Gcd(digitSum, x);
    if g > 1 {
      return;
    }
    x := x + 1;
  }
}

method Main()
  decreases *
{
  // ===== SPEC POSITIVE TESTS =====
  // Each tests GcdSumMeetsSpec(n, correct_result) == true
  expect GcdSumMeetsSpec(1, 2), "spec positive 1";
  expect GcdSumMeetsSpec(2, 2), "spec positive 2";
  expect GcdSumMeetsSpec(3, 3), "spec positive 3";
  expect GcdSumMeetsSpec(5, 5), "spec positive 4";
  expect GcdSumMeetsSpec(7, 7), "spec positive 5";
  expect GcdSumMeetsSpec(9, 9), "spec positive 6";
  expect GcdSumMeetsSpec(10, 12), "spec positive 7";
  expect GcdSumMeetsSpec(11, 12), "spec positive 8";
  expect GcdSumMeetsSpec(12, 12), "spec positive 9";
  expect GcdSumMeetsSpec(13, 15), "spec positive 10";
  expect GcdSumMeetsSpec(15, 15), "spec positive 11";
  expect GcdSumMeetsSpec(18, 18), "spec positive 12";
  expect GcdSumMeetsSpec(20, 20), "spec positive 13";

  // ===== SPEC NEGATIVE TESTS =====
  // Each tests GcdSumMeetsSpec(n, wrong_result) == false
  expect !GcdSumMeetsSpec(11, 13), "spec negative 1";   // wrong 13, correct 12
  expect !GcdSumMeetsSpec(1, 3), "spec negative 2";     // wrong 3, correct 2
  expect !GcdSumMeetsSpec(50, 51), "spec negative 3";   // wrong 51, correct 50
  expect !GcdSumMeetsSpec(2, 3), "spec negative 4";     // wrong 3, correct 2
  expect !GcdSumMeetsSpec(7, 8), "spec negative 5";     // wrong 8, correct 7
  expect !GcdSumMeetsSpec(1, 3), "spec negative 6";     // wrong 3, correct 2
  expect !GcdSumMeetsSpec(12, 13), "spec negative 7";   // wrong 13, correct 12
  expect !GcdSumMeetsSpec(9, 10), "spec negative 8";    // wrong 10, correct 9
  expect !GcdSumMeetsSpec(3, 4), "spec negative 9";     // wrong 4, correct 3
  expect !GcdSumMeetsSpec(41, 43), "spec negative 10";  // wrong 43, correct 42

  // ===== IMPLEMENTATION TESTS =====
  // Test 1
  var r1 := GcdSum(11);
  expect r1 == 12, "impl test 1a failed";
  var r2 := GcdSum(31);
  expect r2 == 33, "impl test 1b failed";
  var r3 := GcdSum(75);
  expect r3 == 75, "impl test 1c failed";

  // Test 2
  var r4 := GcdSum(1);
  expect r4 == 2, "impl test 2 failed";

  // Test 3
  var r5 := GcdSum(50);
  expect r5 == 50, "impl test 3 failed";

  // Test 4
  var r6 := GcdSum(2);
  expect r6 == 2, "impl test 4a failed";
  var r7 := GcdSum(10);
  expect r7 == 12, "impl test 4b failed";
  var r8 := GcdSum(15);
  expect r8 == 15, "impl test 4c failed";
  var r9 := GcdSum(33);
  expect r9 == 33, "impl test 4d failed";
  var r10 := GcdSum(49);
  expect r10 == 50, "impl test 4e failed";

  // Test 5
  var r11 := GcdSum(7);
  expect r11 == 7, "impl test 5 failed";

  // Test 6
  var r12 := GcdSum(1);
  expect r12 == 2, "impl test 6a failed";
  var r13 := GcdSum(2);
  expect r13 == 2, "impl test 6b failed";

  // Test 7
  var r14 := GcdSum(12);
  expect r14 == 12, "impl test 7a failed";
  var r15 := GcdSum(24);
  expect r15 == 24, "impl test 7b failed";
  var r16 := GcdSum(36);
  expect r16 == 36, "impl test 7c failed";
  var r17 := GcdSum(48);
  expect r17 == 48, "impl test 7d failed";

  // Test 8
  var r18 := GcdSum(9);
  expect r18 == 9, "impl test 8a failed";
  var r19 := GcdSum(18);
  expect r19 == 18, "impl test 8b failed";
  var r20 := GcdSum(27);
  expect r20 == 27, "impl test 8c failed";

  // Test 9
  var r21 := GcdSum(3);
  expect r21 == 3, "impl test 9a failed";
  var r22 := GcdSum(5);
  expect r22 == 5, "impl test 9b failed";
  var r23 := GcdSum(13);
  expect r23 == 15, "impl test 9c failed";
  var r24 := GcdSum(20);
  expect r24 == 20, "impl test 9d failed";
  var r25 := GcdSum(37);
  expect r25 == 39, "impl test 9e failed";
  var r26 := GcdSum(45);
  expect r26 == 45, "impl test 9f failed";

  // Test 10
  var r27 := GcdSum(41);
  expect r27 == 42, "impl test 10a failed";
  var r28 := GcdSum(50);
  expect r28 == 50, "impl test 10b failed";

  print "All tests passed\n";
}