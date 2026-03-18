predicate IsProperDivisor(d: int, n: int) {
  1 <= d && d < n && n % d == 0
}

predicate ValidStep(from: int, to: int) {
  from > 1 && (
    to == from - 1 ||
    (exists d | 1 <= d < from :: IsProperDivisor(d, from) && to == from / d)
  )
}

predicate Reachable(n: int, steps: nat)
  decreases steps
{
  if steps == 0 then n == 1
  else n > 1 && (exists next | 1 <= next < n :: ValidStep(n, next) && Reachable(next, steps - 1))
}

predicate IsMinReachable(n: int, moves: int) {
  moves >= 0 && Reachable(n, moves) && forall k | 0 <= k < moves :: !Reachable(n, k)
}

method SubtractOrDivide(n: int) returns (moves: int)
  requires n >= 1
  ensures moves >= 0
  ensures Reachable(n, moves)
  ensures forall k | 0 <= k < moves :: !Reachable(n, k)
{
  if n == 1 {
    return 0;
  } else if n == 2 {
    return 1;
  } else if n % 2 == 0 || n == 3 {
    return 2;
  } else {
    return 3;
  }
}

method ToString(n: int) returns (s: string)
{
  if n < 0 {
    var pos := ToString(-n);
    return "-" + pos;
  }
  if n < 10 {
    var digits := ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];
    return [digits[n]];
  }
  var rest := ToString(n / 10);
  var digits := ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];
  return rest + [digits[n % 10]];
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  expect IsMinReachable(1, 0), "spec positive 1";
  expect IsMinReachable(2, 1), "spec positive 2";
  expect IsMinReachable(3, 2), "spec positive 3";
  expect IsMinReachable(4, 2), "spec positive 4";
  expect IsMinReachable(6, 2), "spec positive 5";
  expect IsMinReachable(9, 3), "spec positive 6";
  expect IsMinReachable(10, 2), "spec positive 7";

  // === SPEC NEGATIVE TESTS ===
  expect !IsMinReachable(1, 1), "spec negative 1";   // correct=0, wrong=1
  expect !IsMinReachable(2, 2), "spec negative 2";   // correct=1, wrong=2
  expect !IsMinReachable(3, 3), "spec negative 3";   // correct=2, wrong=3
  expect !IsMinReachable(10, 3), "spec negative 4";  // correct=2, wrong=3
  expect !IsMinReachable(9, 4), "spec negative 5";   // correct=3, wrong=4 (scaled from n=25,49)

  // === IMPLEMENTATION TESTS ===
  var r1 := SubtractOrDivide(1);
  var s1 := ToString(r1);
  expect r1 == 0, "impl test 1 failed: n=1, expected 0, got " + s1;

  var r2 := SubtractOrDivide(2);
  var s2 := ToString(r2);
  expect r2 == 1, "impl test 2 failed: n=2, expected 1, got " + s2;

  var r3 := SubtractOrDivide(3);
  var s3 := ToString(r3);
  expect r3 == 2, "impl test 3 failed: n=3, expected 2, got " + s3;

  var r4 := SubtractOrDivide(4);
  var s4 := ToString(r4);
  expect r4 == 2, "impl test 4 failed: n=4, expected 2, got " + s4;

  var r5 := SubtractOrDivide(6);
  var s5 := ToString(r5);
  expect r5 == 2, "impl test 5 failed: n=6, expected 2, got " + s5;

  var r6 := SubtractOrDivide(9);
  var s6 := ToString(r6);
  expect r6 == 3, "impl test 6 failed: n=9, expected 3, got " + s6;

  var r7 := SubtractOrDivide(10);
  var s7 := ToString(r7);
  expect r7 == 2, "impl test 7 failed: n=10, expected 2, got " + s7;

  var r8 := SubtractOrDivide(25);
  var s8 := ToString(r8);
  expect r8 == 3, "impl test 8 failed: n=25, expected 3, got " + s8;

  var r9 := SubtractOrDivide(49);
  var s9 := ToString(r9);
  expect r9 == 3, "impl test 9 failed: n=49, expected 3, got " + s9;

  print "All tests passed\n";
}