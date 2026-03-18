function BitAnd(a: int, b: int): int
  requires a >= 0 && b >= 0
  decreases a + b
{
  if a == 0 || b == 0 then 0
  else 2 * BitAnd(a / 2, b / 2) + (if a % 2 == 1 && b % 2 == 1 then 1 else 0)
}

function AndRange(lo: int, hi: int): int
  requires 0 <= lo <= hi
  decreases hi - lo
{
  if lo == hi then hi
  else BitAnd(AndRange(lo, hi - 1), hi)
}

method AndThenThereWereK(n: int) returns (k: int)
  requires n >= 1
  ensures 0 <= k <= n
  ensures AndRange(k, n) == 0
  ensures forall k' | k < k' <= n :: AndRange(k', n) != 0
{
  var p := 1;
  while p * 2 <= n
    decreases n - p
  {
    p := p * 2;
  }
  k := p - 1;
}

// Helper: iteratively checks the forall ensures condition
method CheckForall(k: int, n: int) returns (ok: bool)
  requires n >= 1
  requires 0 <= k <= n
{
  var i := k + 1;
  while i <= n
  {
    if AndRange(i, n) == 0 {
      return false;
    }
    i := i + 1;
  }
  return true;
}

// Checks all three ensures conditions for a given (n, k) pair
method CheckSpec(n: int, k: int) returns (valid: bool)
  requires n >= 1
  requires 0 <= k <= n
{
  if AndRange(k, n) != 0 {
    return false;
  }
  var forallOk := CheckForall(k, n);
  return forallOk;
}

method Main()
{
  var ok: bool;
  var r: int;

  // ============================================
  // SPEC POSITIVE TESTS
  // Verify the ensures predicates accept correct (n, k) pairs.
  // Small inputs only to keep AndRange/forall tractable.
  // ============================================

  ok := CheckSpec(1, 0);
  expect ok, "spec positive 1: n=1, k=0";

  ok := CheckSpec(2, 1);
  expect ok, "spec positive 2: n=2, k=1";

  ok := CheckSpec(3, 1);
  expect ok, "spec positive 3: n=3, k=1";

  ok := CheckSpec(7, 3);
  expect ok, "spec positive 4: n=7, k=3";

  ok := CheckSpec(10, 7);
  expect ok, "spec positive 5: n=10, k=7";

  ok := CheckSpec(16, 15);
  expect ok, "spec positive 6: n=16, k=15";

  ok := CheckSpec(32, 31);
  expect ok, "spec positive 7: n=32, k=31";

  // ============================================
  // SPEC NEGATIVE TESTS
  // Verify the ensures predicates REJECT wrong k values.
  // Each wrong_k causes AndRange(wrong_k, n) != 0,
  // so the full spec conjunction is false.
  // ============================================

  ok := CheckSpec(1, 1);
  expect !ok, "spec negative 1: n=1, wrong_k=1 (correct=0)";

  ok := CheckSpec(2, 2);
  expect !ok, "spec negative 2: n=2, wrong_k=2 (correct=1)";

  ok := CheckSpec(3, 2);
  expect !ok, "spec negative 3: n=3, wrong_k=2 (correct=1)";

  ok := CheckSpec(7, 4);
  expect !ok, "spec negative 4: n=7, wrong_k=4 (correct=3)";

  ok := CheckSpec(10, 8);
  expect !ok, "spec negative 5: n=10, wrong_k=8 (correct=7)";

  ok := CheckSpec(16, 16);
  expect !ok, "spec negative 6: n=16, wrong_k=16 (correct=15)";

  ok := CheckSpec(32, 32);
  expect !ok, "spec negative 7: n=32, wrong_k=32 (correct=31)";

  // ============================================
  // IMPLEMENTATION TESTS
  // Call the method with full-size inputs and check outputs.
  // ============================================

  r := AndThenThereWereK(1);
  expect r == 0, "impl test 1: AndThenThereWereK(1)";

  r := AndThenThereWereK(2);
  expect r == 1, "impl test 2: AndThenThereWereK(2)";

  r := AndThenThereWereK(3);
  expect r == 1, "impl test 3: AndThenThereWereK(3)";

  r := AndThenThereWereK(5);
  expect r == 3, "impl test 4: AndThenThereWereK(5)";

  r := AndThenThereWereK(7);
  expect r == 3, "impl test 5: AndThenThereWereK(7)";

  r := AndThenThereWereK(10);
  expect r == 7, "impl test 6: AndThenThereWereK(10)";

  r := AndThenThereWereK(16);
  expect r == 15, "impl test 7: AndThenThereWereK(16)";

  r := AndThenThereWereK(17);
  expect r == 15, "impl test 8: AndThenThereWereK(17)";

  r := AndThenThereWereK(32);
  expect r == 31, "impl test 9: AndThenThereWereK(32)";

  r := AndThenThereWereK(48);
  expect r == 31, "impl test 10: AndThenThereWereK(48)";

  r := AndThenThereWereK(50);
  expect r == 31, "impl test 11: AndThenThereWereK(50)";

  r := AndThenThereWereK(99888383);
  expect r == 67108863, "impl test 12: AndThenThereWereK(99888383)";

  print "All tests passed\n";
}