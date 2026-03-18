function InitialList(n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else InitialList(n - 1) + [n]
}

function RemoveAtIndex(s: seq<int>, idx: nat): seq<int>
  requires idx < |s|
{
  s[..idx] + s[idx + 1..]
}

function Simulate(remaining: seq<int>, step: nat): seq<int>
  decreases |remaining|
{
  if step == 0 || step > |remaining| then remaining
  else Simulate(RemoveAtIndex(remaining, step - 1), step + 1)
}

function FinalList(n: nat): seq<int>
{
  Simulate(InitialList(n), 1)
}

method RemoveAProgression(n: int, x: int) returns (result: int)
  requires n >= 1
  requires x >= 1
  requires x <= |FinalList(n)|
  ensures result == FinalList(n)[x - 1]
{
  return x * 2;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Top-level ensures predicate: result == FinalList(n)[x - 1]
  // Using small n to keep FinalList evaluation tractable.

  // From Test 1a: (3,1)->2
  expect FinalList(3)[0] == 2, "spec positive 1";
  // From Test 1b: (4,2)->4
  expect FinalList(4)[1] == 4, "spec positive 2";
  // From Test 1c: (69,6)->12, scaled to (12,6)->12
  expect FinalList(12)[5] == 12, "spec positive 3";
  // From Test 2a: (10^9,1)->2, scaled to (2,1)->2
  expect FinalList(2)[0] == 2, "spec positive 4";
  // From Test 2b: (10^9,5*10^8)->10^9, scaled to (6,3)->6
  expect FinalList(6)[2] == 6, "spec positive 5";
  // From Test 3: (2441139,10)->20, scaled to (10,5)->10
  expect FinalList(10)[4] == 10, "spec positive 6";
  // From Test 9: (2441139,2)->4, scaled to (8,4)->8
  expect FinalList(8)[3] == 8, "spec positive 7";

  // === SPEC NEGATIVE TESTS ===
  // Ensures predicate must reject wrong outputs.

  // From Neg 1: (3,1) wrong=3, correct=2
  expect FinalList(3)[0] != 3, "spec negative 1";
  // From Neg 2: (10^9,1) wrong=3, scaled to (2,1) wrong=3
  expect FinalList(2)[0] != 3, "spec negative 2";
  // From Neg 3: (2441139,10) wrong=21, scaled to (10,5) wrong=11
  expect FinalList(10)[4] != 11, "spec negative 3";
  // From Neg 4: (2441139,1) wrong=3, scaled to (4,1) wrong=3
  expect FinalList(4)[0] != 3, "spec negative 4";
  // From Neg 5: (244139,1) wrong=3, scaled to (6,1) wrong=3
  expect FinalList(6)[0] != 3, "spec negative 5";
  // From Neg 6: (2441139,12) wrong=25, scaled to (8,4) wrong=9
  expect FinalList(8)[3] != 9, "spec negative 6";
  // From Neg 7: (241139,1) wrong=3, scaled to (8,1) wrong=3
  expect FinalList(8)[0] != 3, "spec negative 7";
  // From Neg 8: (244119,1) wrong=3, scaled to (10,1) wrong=3
  expect FinalList(10)[0] != 3, "spec negative 8";
  // From Neg 9: (2441139,2) wrong=5, scaled to (4,2) wrong=5
  expect FinalList(4)[1] != 5, "spec negative 9";
  // From Neg 10: (2451199,2) wrong=5, scaled to (6,2) wrong=5
  expect FinalList(6)[1] != 5, "spec negative 10";

  // === IMPLEMENTATION TESTS ===

  // Test 1
  var r1 := RemoveAProgression(3, 1);
  expect r1 == 2, "impl test 1a failed";
  var r2 := RemoveAProgression(4, 2);
  expect r2 == 4, "impl test 1b failed";
  var r3 := RemoveAProgression(69, 6);
  expect r3 == 12, "impl test 1c failed";

  // Test 2
  var r4 := RemoveAProgression(1000000000, 1);
  expect r4 == 2, "impl test 2a failed";
  var r5 := RemoveAProgression(1000000000, 500000000);
  expect r5 == 1000000000, "impl test 2b failed";

  // Test 3
  var r6 := RemoveAProgression(2441139, 10);
  expect r6 == 20, "impl test 3 failed";

  // Test 4
  var r7 := RemoveAProgression(2441139, 1);
  expect r7 == 2, "impl test 4 failed";

  // Test 5
  var r8 := RemoveAProgression(244139, 1);
  expect r8 == 2, "impl test 5 failed";

  // Test 6
  var r9 := RemoveAProgression(2441139, 12);
  expect r9 == 24, "impl test 6 failed";

  // Test 7
  var r10 := RemoveAProgression(241139, 1);
  expect r10 == 2, "impl test 7 failed";

  // Test 8
  var r11 := RemoveAProgression(244119, 1);
  expect r11 == 2, "impl test 8 failed";

  // Test 9
  var r12 := RemoveAProgression(2441139, 2);
  expect r12 == 4, "impl test 9 failed";

  // Test 10
  var r13 := RemoveAProgression(2451199, 2);
  expect r13 == 4, "impl test 10 failed";

  // Test 11
  var r14 := RemoveAProgression(2452199, 2);
  expect r14 == 4, "impl test 11 failed";

  print "All tests passed\n";
}