// Spec functions
function CountVal(s: seq<int>, v: int): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountVal(s[..|s|-1], v) + (if s[|s|-1] == v then 1 else 0)
}

predicate CanExitAfter(doors: seq<int>, k: int)
  requires 0 <= k <= |doors|
{
  CountVal(doors[..k], 0) == CountVal(doors, 0) ||
  CountVal(doors[..k], 1) == CountVal(doors, 1)
}

// Implementation
method TheDoors(n: int, doors: seq<int>) returns (k: int)
  requires n == |doors|
  requires n >= 2
  requires forall i | 0 <= i < n :: doors[i] == 0 || doors[i] == 1
  requires CountVal(doors, 0) >= 1
  requires CountVal(doors, 1) >= 1
  ensures 1 <= k <= n
  ensures CanExitAfter(doors, k)
  ensures forall j | 0 <= j < k :: !CanExitAfter(doors, j)
{
  var a := 0;
  var b := 0;
  var i := 0;
  while i < n {
    if doors[i] == 0 {
      a := a + 1;
    } else {
      b := b + 1;
    }
    i := i + 1;
  }
  var x := 0;
  var y := 0;
  i := 0;
  while i < n {
    if doors[i] == 1 {
      y := y + 1;
    } else {
      x := x + 1;
    }
    if x == a || y == b {
      return i + 1;
    }
    i := i + 1;
  }
  return 0;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // For each small test pair, verify CanExitAfter holds at correct k
  // and minimality (no earlier exit possible)

  // Spec positive 1: [1,0] -> k=1
  expect CanExitAfter([1,0], 1), "spec positive 1 - CanExitAfter";
  expect forall j | 0 <= j < 1 :: !CanExitAfter([1,0], j), "spec positive 1 - minimality";

  // Spec positive 2: [0,1] -> k=1
  expect CanExitAfter([0,1], 1), "spec positive 2 - CanExitAfter";
  expect forall j | 0 <= j < 1 :: !CanExitAfter([0,1], j), "spec positive 2 - minimality";

  // Spec positive 3: [0,0,1] -> k=2
  expect CanExitAfter([0,0,1], 2), "spec positive 3 - CanExitAfter";
  expect forall j | 0 <= j < 2 :: !CanExitAfter([0,0,1], j), "spec positive 3 - minimality";

  // Spec positive 4: [0,1,1] -> k=1
  expect CanExitAfter([0,1,1], 1), "spec positive 4 - CanExitAfter";
  expect forall j | 0 <= j < 1 :: !CanExitAfter([0,1,1], j), "spec positive 4 - minimality";

  // Spec positive 5: [0,1,0] -> k=2
  expect CanExitAfter([0,1,0], 2), "spec positive 5 - CanExitAfter";
  expect forall j | 0 <= j < 2 :: !CanExitAfter([0,1,0], j), "spec positive 5 - minimality";

  // Spec positive 6: [1,0,0] -> k=1
  expect CanExitAfter([1,0,0], 1), "spec positive 6 - CanExitAfter";
  expect forall j | 0 <= j < 1 :: !CanExitAfter([1,0,0], j), "spec positive 6 - minimality";

  // Spec positive 7: [1,0,1] -> k=2
  expect CanExitAfter([1,0,1], 2), "spec positive 7 - CanExitAfter";
  expect forall j | 0 <= j < 2 :: !CanExitAfter([1,0,1], j), "spec positive 7 - minimality";

  // Spec positive 8: [1,1,0] -> k=2
  expect CanExitAfter([1,1,0], 2), "spec positive 8 - CanExitAfter";
  expect forall j | 0 <= j < 2 :: !CanExitAfter([1,1,0], j), "spec positive 8 - minimality";

  // ===== SPEC NEGATIVE TESTS =====
  // For each small negative pair, verify the wrong k fails minimality

  // Spec negative 1: [0,1,0], wrong k=3 (correct=2)
  expect !(forall j | 0 <= j < 3 :: !CanExitAfter([0,1,0], j)), "spec negative 1";

  // Spec negative 2: [1,0], wrong k=2 (correct=1)
  expect !(forall j | 0 <= j < 2 :: !CanExitAfter([1,0], j)), "spec negative 2";

  // Spec negative 3: [0,1], wrong k=2 (correct=1)
  expect !(forall j | 0 <= j < 2 :: !CanExitAfter([0,1], j)), "spec negative 3";

  // Spec negative 4: [0,0,1], wrong k=3 (correct=2)
  expect !(forall j | 0 <= j < 3 :: !CanExitAfter([0,0,1], j)), "spec negative 4";

  // Spec negative 5: [0,1,1], wrong k=2 (correct=1)
  expect !(forall j | 0 <= j < 2 :: !CanExitAfter([0,1,1], j)), "spec negative 5";

  // ===== IMPLEMENTATION TESTS =====
  var r1 := TheDoors(5, [0, 0, 1, 0, 0]);
  expect r1 == 3, "impl test 1 failed";

  var r2 := TheDoors(4, [1, 0, 0, 1]);
  expect r2 == 3, "impl test 2 failed";

  var r3 := TheDoors(5, [1, 1, 0, 0, 0]);
  expect r3 == 2, "impl test 3 failed";

  var r4 := TheDoors(3, [0, 1, 0]);
  expect r4 == 2, "impl test 4 failed";

  var r5 := TheDoors(16, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]);
  expect r5 == 15, "impl test 5 failed";

  var r6 := TheDoors(250, [1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1]);
  expect r6 == 249, "impl test 6 failed";

  var r7 := TheDoors(2, [1, 0]);
  expect r7 == 1, "impl test 7 failed";

  var r8 := TheDoors(2, [0, 1]);
  expect r8 == 1, "impl test 8 failed";

  var r9 := TheDoors(3, [0, 0, 1]);
  expect r9 == 2, "impl test 9 failed";

  var r10 := TheDoors(3, [0, 1, 1]);
  expect r10 == 1, "impl test 10 failed";

  var r11 := TheDoors(3, [1, 0, 0]);
  expect r11 == 1, "impl test 11 failed";

  var r12 := TheDoors(3, [1, 0, 1]);
  expect r12 == 2, "impl test 12 failed";

  var r13 := TheDoors(3, [1, 1, 0]);
  expect r13 == 2, "impl test 13 failed";

  print "All tests passed\n";
}