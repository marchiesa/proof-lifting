function NumDigits(n: int): nat
  requires n > 0
  decreases n
{
  if n < 10 then 1 else 1 + NumDigits(n / 10)
}

function Pow2(d: nat): nat
  decreases d
{
  if d == 0 then 1 else 2 * Pow2(d - 1)
}

function BinToDec(i: nat): nat
  decreases i
{
  if i == 0 then 0
  else BinToDec(i / 2) * 10 + i % 2
}

predicate CanDecompose(n: int, k: nat, bdBound: nat)
  decreases k
{
  if k == 0 then n == 0
  else exists i | 1 <= i < bdBound ::
    BinToDec(i) <= n && CanDecompose(n - BinToDec(i), k - 1, bdBound)
}

method BinaryDecimal(n: int) returns (result: int)
  requires n > 0
  ensures result >= 1
  ensures CanDecompose(n, result, Pow2(NumDigits(n)))
  ensures forall k | 0 <= k < result :: !CanDecompose(n, k, Pow2(NumDigits(n)))
{
  result := 0;
  var num := n;
  while num > 0 {
    var digit := num % 10;
    if digit > result {
      result := digit;
    }
    num := num / 10;
  }
}

// Checks all three ensures conditions: result >= 1, CanDecompose, and minimality
method MeetsSpec(n: int, result: nat) returns (ok: bool)
  requires n > 0
{
  if result < 1 { return false; }
  var bd := Pow2(NumDigits(n));
  if !CanDecompose(n, result, bd) { return false; }
  var k: nat := 0;
  while k < result {
    if CanDecompose(n, k, bd) { return false; }
    k := k + 1;
  }
  return true;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  var sp1 := MeetsSpec(1, 1);
  expect sp1, "spec positive 1 failed";

  var sp2 := MeetsSpec(2, 2);
  expect sp2, "spec positive 2 failed";

  var sp3 := MeetsSpec(3, 3);
  expect sp3, "spec positive 3 failed";

  var sp4 := MeetsSpec(5, 5);
  expect sp4, "spec positive 4 failed";

  var sp5 := MeetsSpec(9, 9);
  expect sp5, "spec positive 5 failed";

  var sp6 := MeetsSpec(10, 1);
  expect sp6, "spec positive 6 failed";

  var sp7 := MeetsSpec(11, 1);
  expect sp7, "spec positive 7 failed";

  var sp8 := MeetsSpec(25, 5);
  expect sp8, "spec positive 8 failed";

  var sp9 := MeetsSpec(50, 5);
  expect sp9, "spec positive 9 failed";

  var sp10 := MeetsSpec(121, 2);
  expect sp10, "spec positive 10 failed";

  var sp11 := MeetsSpec(21, 2);
  expect sp11, "spec positive 11 failed";

  // === SPEC NEGATIVE TESTS ===
  var sn1 := MeetsSpec(1, 2);
  expect !sn1, "spec negative 1 failed";

  var sn2 := MeetsSpec(10, 2);
  expect !sn2, "spec negative 2 failed";

  var sn3 := MeetsSpec(11, 2);
  expect !sn3, "spec negative 3 failed";

  var sn4 := MeetsSpec(9, 10);
  expect !sn4, "spec negative 4 failed";

  var sn5 := MeetsSpec(121, 3);
  expect !sn5, "spec negative 5 failed";

  var sn6 := MeetsSpec(25, 6);
  expect !sn6, "spec negative 6 failed";

  var sn7 := MeetsSpec(50, 6);
  expect !sn7, "spec negative 7 failed";

  var sn8 := MeetsSpec(49, 10);
  expect !sn8, "spec negative 8 failed";

  // === IMPLEMENTATION TESTS ===
  // Test 1
  var r1 := BinaryDecimal(121);
  expect r1 == 2, "impl test 1a failed";
  var r2 := BinaryDecimal(5);
  expect r2 == 5, "impl test 1b failed";
  var r3 := BinaryDecimal(1000000000);
  expect r3 == 1, "impl test 1c failed";

  // Test 2
  var r4 := BinaryDecimal(1);
  expect r4 == 1, "impl test 2 failed";

  // Test 3
  var r5 := BinaryDecimal(10);
  expect r5 == 1, "impl test 3 failed";

  // Test 4
  var r6 := BinaryDecimal(9);
  expect r6 == 9, "impl test 4 failed";

  // Test 5
  var r7 := BinaryDecimal(11);
  expect r7 == 1, "impl test 5 failed";

  // Test 6
  var r8 := BinaryDecimal(25);
  expect r8 == 5, "impl test 6 failed";

  // Test 7
  var r9 := BinaryDecimal(50);
  expect r9 == 5, "impl test 7 failed";

  // Test 8
  var r10 := BinaryDecimal(1);
  expect r10 == 1, "impl test 8a failed";
  var r11 := BinaryDecimal(2);
  expect r11 == 2, "impl test 8b failed";
  var r12 := BinaryDecimal(3);
  expect r12 == 3, "impl test 8c failed";

  // Test 9
  var r13 := BinaryDecimal(9);
  expect r13 == 9, "impl test 9a failed";
  var r14 := BinaryDecimal(19);
  expect r14 == 9, "impl test 9b failed";
  var r15 := BinaryDecimal(21);
  expect r15 == 2, "impl test 9c failed";
  var r16 := BinaryDecimal(30);
  expect r16 == 3, "impl test 9d failed";
  var r17 := BinaryDecimal(45);
  expect r17 == 5, "impl test 9e failed";

  // Test 10
  var r18 := BinaryDecimal(49);
  expect r18 == 9, "impl test 10a failed";
  var r19 := BinaryDecimal(50);
  expect r19 == 5, "impl test 10b failed";

  print "All tests passed\n";
}