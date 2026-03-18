predicate ReachableInSteps(n: int, steps: nat)
  decreases steps
{
  if steps == 0 then
    n == 1
  else
    (n % 2 == 0 && ReachableInSteps(n / 2, steps - 1)) ||
    (n % 3 == 0 && ReachableInSteps(2 * n / 3, steps - 1)) ||
    (n % 5 == 0 && ReachableInSteps(4 * n / 5, steps - 1))
}

predicate IsMinSteps(n: int, steps: nat)
{
  ReachableInSteps(n, steps) &&
  forall k: nat | k < steps :: !ReachableInSteps(n, k)
}

predicate Impossible(n: int)
{
  forall k: nat | 0 <= k <= n :: !ReachableInSteps(n, k)
}

method DivideIt(n: int) returns (ans: int)
  requires n >= 1
  ensures (ans == -1 && Impossible(n)) ||
          (ans >= 0 && IsMinSteps(n, ans as nat))
{
  ans := 0;
  var m := n;
  while m % 2 == 0 {
    ans := ans + 1;
    m := m / 2;
  }
  while m % 3 == 0 {
    ans := ans + 2;
    m := m / 3;
  }
  while m % 5 == 0 {
    ans := ans + 3;
    m := m / 5;
  }
  if m != 1 {
    ans := -1;
  }
  return;
}

method Main() {
  // === SPEC POSITIVE TESTS ===
  // Small inputs where IsMinSteps / Impossible should accept
  expect IsMinSteps(1, 0), "spec positive 1: IsMinSteps(1, 0)";
  expect IsMinSteps(2, 1), "spec positive 2: IsMinSteps(2, 1)";
  expect IsMinSteps(3, 2), "spec positive 3: IsMinSteps(3, 2)";
  expect IsMinSteps(4, 2), "spec positive 4: IsMinSteps(4, 2)";
  expect IsMinSteps(5, 3), "spec positive 5: IsMinSteps(5, 3)";
  expect IsMinSteps(6, 3), "spec positive 6: IsMinSteps(6, 3)";
  expect Impossible(7),    "spec positive 7: Impossible(7)";
  expect Impossible(11),   "spec positive 8: Impossible(11)";

  // === SPEC NEGATIVE TESTS ===
  // Small inputs where IsMinSteps / Impossible should reject
  expect !IsMinSteps(1, 1), "spec negative 1: !IsMinSteps(1, 1)";
  expect !IsMinSteps(2, 0), "spec negative 2: !IsMinSteps(2, 0)";
  expect !IsMinSteps(2, 2), "spec negative 3: !IsMinSteps(2, 2)";
  expect !IsMinSteps(3, 1), "spec negative 4: !IsMinSteps(3, 1)";
  expect !IsMinSteps(4, 1), "spec negative 5: !IsMinSteps(4, 1)";
  expect !IsMinSteps(5, 2), "spec negative 6: !IsMinSteps(5, 2)";
  expect !Impossible(1),    "spec negative 7: !Impossible(1)";
  expect !Impossible(2),    "spec negative 8: !Impossible(2)";

  // === IMPLEMENTATION TESTS ===
  var r1 := DivideIt(1);
  expect r1 == 0, "impl test 1: n=1 expected 0";

  var r2 := DivideIt(10);
  expect r2 == 4, "impl test 2: n=10 expected 4";

  var r3 := DivideIt(25);
  expect r3 == 6, "impl test 3: n=25 expected 6";

  var r4 := DivideIt(30);
  expect r4 == 6, "impl test 4: n=30 expected 6";

  var r5 := DivideIt(14);
  expect r5 == -1, "impl test 5: n=14 expected -1";

  var r6 := DivideIt(27);
  expect r6 == 6, "impl test 6: n=27 expected 6";

  var r7 := DivideIt(1000000000000000000);
  expect r7 == 72, "impl test 7: n=10^18 expected 72";

  var r8 := DivideIt(22876792454961);
  expect r8 == 56, "impl test 8: n=22876792454961 expected 56";

  var r9 := DivideIt(70745089028899904);
  expect r9 == -1, "impl test 9: n=70745089028899904 expected -1";

  var r10 := DivideIt(576460752303423487);
  expect r10 == -1, "impl test 10: n=576460752303423487 expected -1";

  print "All tests passed\n";
}