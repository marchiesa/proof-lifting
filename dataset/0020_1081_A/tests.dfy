predicate ValidMove(n: int, x: int)
{
  1 <= x < n && n % x != 0
}

predicate Reachable(start: int, target: int, steps: nat)
  decreases steps
{
  start >= 1 && target >= 1 &&
  (start == target ||
   (steps > 0 &&
    exists x | 1 <= x < start :: ValidMove(start, x) && Reachable(start - x, target, steps - 1)))
}

predicate IsMinReachable(v: int, result: int)
{
  v >= 1 && result >= 1 &&
  Reachable(v, result, v) &&
  forall r | 1 <= r < result :: !Reachable(v, r, v)
}

method DefiniteGame(v: int) returns (result: int)
  requires v >= 1
  ensures IsMinReachable(v, result)
{
  if v == 2 {
    return 2;
  } else {
    return 1;
  }
}

method Main()
{
  // === SPEC POSITIVE tests (small inputs, testing IsMinReachable) ===
  expect IsMinReachable(1, 1), "spec positive 1";   // v=1 -> 1
  expect IsMinReachable(2, 2), "spec positive 2";   // v=2 -> 2
  expect IsMinReachable(3, 1), "spec positive 3";   // v=3 -> 1
  expect IsMinReachable(4, 1), "spec positive 4";   // v=4 -> 1
  expect IsMinReachable(5, 1), "spec positive 5";   // v=5 -> 1

  // === SPEC NEGATIVE tests (small inputs, wrong outputs rejected) ===
  expect !IsMinReachable(1, 2), "spec negative 1";  // v=1, wrong=2
  expect !IsMinReachable(3, 2), "spec negative 2";  // v=3, wrong=2
  expect !IsMinReachable(4, 2), "spec negative 3";  // v=4, wrong=2
  expect !IsMinReachable(5, 2), "spec negative 4";  // v=5, wrong=2
  expect !IsMinReachable(2, 3), "spec negative 5";  // v=2, wrong=3

  // === IMPLEMENTATION tests (full-size inputs) ===
  var r1 := DefiniteGame(8);
  expect r1 == 1, "impl test 1 failed";

  var r2 := DefiniteGame(1);
  expect r2 == 1, "impl test 2 failed";

  var r3 := DefiniteGame(4);
  expect r3 == 1, "impl test 3 failed";

  var r4 := DefiniteGame(3);
  expect r4 == 1, "impl test 4 failed";

  var r5 := DefiniteGame(158260522);
  expect r5 == 1, "impl test 5 failed";

  var r6 := DefiniteGame(2);
  expect r6 == 2, "impl test 6 failed";

  var r7 := DefiniteGame(1000000000);
  expect r7 == 1, "impl test 7 failed";

  var r8 := DefiniteGame(5);
  expect r8 == 1, "impl test 8 failed";

  var r9 := DefiniteGame(7);
  expect r9 == 1, "impl test 9 failed";

  var r10 := DefiniteGame(9);
  expect r10 == 1, "impl test 10 failed";

  print "All tests passed\n";
}