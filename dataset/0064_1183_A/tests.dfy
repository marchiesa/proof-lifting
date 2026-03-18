function DigitSum(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else n % 10 + DigitSum(n / 10)
}

predicate IsInteresting(n: int)
  requires n >= 0
{
  DigitSum(n) == 18
}

predicate NearestInterestingSpec(a: int, n: int)
  requires a >= 1
  requires n >= 0
{
  n >= a && IsInteresting(n) && forall k | a <= k < n :: !IsInteresting(k)
}

method SumDigits(x: int) returns (s: int)
  requires x >= 0
  ensures s == DigitSum(x)
  decreases *
{
  s := 0;
  var tmp := x;
  while tmp > 0
    decreases *
  {
    s := s + tmp % 10;
    tmp := tmp / 10;
  }
}

method NearestInterestingNumber(a: int) returns (n: int)
  requires a >= 1
  ensures n >= a
  ensures IsInteresting(n)
  ensures forall k | a <= k < n :: !IsInteresting(k)
  decreases *
{
  n := a;
  var s := SumDigits(n);
  while s != 18
    decreases *
  {
    n := n + 1;
    s := SumDigits(n);
  }
}

method Main()
  decreases *
{
  // === SPEC POSITIVE TESTS ===
  // NearestInterestingSpec checks: n >= a, IsInteresting(n), no interesting number in [a, n)
  expect NearestInterestingSpec(99, 99), "spec positive 1";
  expect NearestInterestingSpec(432, 459), "spec positive 2";
  expect NearestInterestingSpec(237, 279), "spec positive 3";
  expect NearestInterestingSpec(42, 99), "spec positive 4";
  expect NearestInterestingSpec(1, 99), "spec positive 5";
  expect NearestInterestingSpec(2, 99), "spec positive 6";
  expect NearestInterestingSpec(909, 909), "spec positive 7";
  expect NearestInterestingSpec(188, 189), "spec positive 8";
  expect NearestInterestingSpec(970, 972), "spec positive 9";
  expect NearestInterestingSpec(898, 909), "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // Wrong outputs are rejected because they are not interesting (digit sum != 18)
  expect !NearestInterestingSpec(432, 460), "spec negative 1";
  expect !NearestInterestingSpec(99, 100), "spec negative 2";
  expect !NearestInterestingSpec(237, 280), "spec negative 3";
  expect !NearestInterestingSpec(42, 100), "spec negative 4";
  expect !NearestInterestingSpec(1, 100), "spec negative 5";
  expect !NearestInterestingSpec(2, 100), "spec negative 6";
  expect !NearestInterestingSpec(1000, 1099), "spec negative 7";
  expect !NearestInterestingSpec(898, 928), "spec negative 8";
  expect !NearestInterestingSpec(997, 1099), "spec negative 9";
  expect !NearestInterestingSpec(999, 1099), "spec negative 10";

  // === IMPLEMENTATION TESTS ===
  var r1 := NearestInterestingNumber(432);
  expect r1 == 459, "impl test 1 failed";

  var r2 := NearestInterestingNumber(99);
  expect r2 == 99, "impl test 2 failed";

  var r3 := NearestInterestingNumber(237);
  expect r3 == 279, "impl test 3 failed";

  var r4 := NearestInterestingNumber(42);
  expect r4 == 99, "impl test 4 failed";

  var r5 := NearestInterestingNumber(1);
  expect r5 == 99, "impl test 5 failed";

  var r6 := NearestInterestingNumber(2);
  expect r6 == 99, "impl test 6 failed";

  var r7 := NearestInterestingNumber(1000);
  expect r7 == 1089, "impl test 7 failed";

  var r8 := NearestInterestingNumber(898);
  expect r8 == 909, "impl test 8 failed";

  var r9 := NearestInterestingNumber(997);
  expect r9 == 1089, "impl test 9 failed";

  var r10 := NearestInterestingNumber(999);
  expect r10 == 1089, "impl test 10 failed";

  print "All tests passed\n";
}