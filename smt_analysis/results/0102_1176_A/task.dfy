// Whether n can be reduced to 1 in exactly `steps` moves,
// where each move is one of the three problem-defined operations.
ghost predicate ReachableInSteps(n: int, steps: nat)
  decreases steps
{
  if steps == 0 then
    n == 1
  else
    (n % 2 == 0 && ReachableInSteps(n / 2, steps - 1)) ||
    (n % 3 == 0 && ReachableInSteps(2 * n / 3, steps - 1)) ||
    (n % 5 == 0 && ReachableInSteps(4 * n / 5, steps - 1))
}

// `steps` is the minimum number of moves to reduce n to 1.
ghost predicate IsMinSteps(n: int, steps: nat)
{
  ReachableInSteps(n, steps) &&
  forall k: nat :: k < steps ==> !ReachableInSteps(n, k)
}

// No sequence of operations can reduce n to 1.
ghost predicate Impossible(n: int)
{
  forall k: nat :: !ReachableInSteps(n, k)
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

method Main()
{
  // Test 1 cases
  var r1 := DivideIt(1);
  expect r1 == 0, "DivideIt(1) failed";

  var r2 := DivideIt(10);
  expect r2 == 4, "DivideIt(10) failed";

  var r3 := DivideIt(25);
  expect r3 == 6, "DivideIt(25) failed";

  var r4 := DivideIt(30);
  expect r4 == 6, "DivideIt(30) failed";

  var r5 := DivideIt(14);
  expect r5 == -1, "DivideIt(14) failed";

  var r6 := DivideIt(27);
  expect r6 == 6, "DivideIt(27) failed";

  var r7 := DivideIt(1000000000000000000);
  expect r7 == 72, "DivideIt(1000000000000000000) failed";

  // Test 2
  var r8 := DivideIt(22876792454961);
  expect r8 == 56, "DivideIt(22876792454961) failed";

  // Test 3
  var r9 := DivideIt(70745089028899904);
  expect r9 == -1, "DivideIt(70745089028899904) failed";

  // Test 4
  var r10 := DivideIt(576460752303423487);
  expect r10 == -1, "DivideIt(576460752303423487) failed";

  // Test 5
  var r11 := DivideIt(1);
  expect r11 == 0, "DivideIt(1) [test5] failed";

  // Test 6
  var r12 := DivideIt(30);
  expect r12 == 6, "DivideIt(30) [test6] failed";

  print "All tests passed\n";
}