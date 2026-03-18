// All pile sizes are within the limit k
predicate AllAtMost(a: seq<int>, k: int) {
  forall i | 0 <= i < |a| :: a[i] <= k
}

// All piles contain at least one candy
predicate AllPositive(a: seq<int>) {
  forall i | 0 <= i < |a| :: a[i] > 0
}

// Models the copy-paste problem structurally:
// Can we perform exactly `steps` copy-paste spells starting from pile
// configuration `a`, where each spell picks two distinct piles (src, dst)
// and does a[dst] := a[dst] + a[src], without any pile ever exceeding k?
predicate CanPerform(a: seq<int>, k: int, steps: nat)
  decreases steps
{
  if steps == 0 then
    true
  else
    |a| >= 2 &&
    exists src: int, dst: int |
      0 <= src < |a| && 0 <= dst < |a| && src != dst &&
      a[dst] + a[src] <= k ::
      CanPerform(a[dst := a[dst] + a[src]], k, steps - 1)
}

method CopyPaste(n: int, k: int, a: seq<int>) returns (maxSpells: int)
  requires n == |a|
  requires |a| > 0
  requires AllPositive(a)
  requires AllAtMost(a, k)
  ensures maxSpells >= 0
  // maxSpells spells are achievable
  ensures CanPerform(a, k, maxSpells)
  // No number of spells beyond maxSpells is achievable
  // (n*k bounds all reachable operation counts since each spell adds >= 1
  //  and total candy across all piles can never exceed n*k)
  ensures forall s: nat | s <= n * k :: CanPerform(a, k, s) ==> s <= maxSpells
{
  var m := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < m {
      m := a[i];
    }
    i := i + 1;
  }

  var out := 0;
  i := 0;
  while i < |a|
  {
    out := out + (k - a[i]) / m;
    i := i + 1;
  }

  out := out - (k - m) / m;
  return out;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // CanPerform(a, k, correct_output) should be true
  // Small inputs only (length 1-3, values 0-5) to keep quantifier enumeration fast

  // From Test 1a/2: [1,1], k=2, correct=1
  expect CanPerform([1, 1], 2, 1), "spec positive 1";

  // From Test 11a: [1,2], k=3, correct=1
  expect CanPerform([1, 2], 3, 1), "spec positive 2";

  // From Test 9: [2,2], k=4, correct=1
  expect CanPerform([2, 2], 4, 1), "spec positive 3";

  // Scaled from Test 3: [1,1], k=3, correct=2
  expect CanPerform([1, 1], 3, 2), "spec positive 4";

  // Scaled from Test 4: [1,2], k=4, correct=2
  expect CanPerform([1, 2], 4, 2), "spec positive 5";

  // Scaled from Test 8: [1,2,2], k=3, correct=2
  expect CanPerform([1, 2, 2], 3, 2), "spec positive 6";

  // Scaled from Test 10: [1,1,2], k=3, correct=3
  expect CanPerform([1, 1, 2], 3, 3), "spec positive 7";

  // ===== SPEC NEGATIVE TESTS =====
  // !CanPerform(a, k, wrong_output) should hold (wrong = correct + 1)
  // Small inputs only

  // From Neg 1/2: [1,1], k=2, wrong=2
  expect !CanPerform([1, 1], 2, 2), "spec negative 1";

  // Scaled Neg for [1,2], k=3, wrong=2
  expect !CanPerform([1, 2], 3, 2), "spec negative 2";

  // From Neg 9: [2,2], k=4, wrong=2
  expect !CanPerform([2, 2], 4, 2), "spec negative 3";

  // Scaled from Neg 3: [1,1], k=3, wrong=3
  expect !CanPerform([1, 1], 3, 3), "spec negative 4";

  // Scaled from Neg 4: [1,2], k=4, wrong=3
  expect !CanPerform([1, 2], 4, 3), "spec negative 5";

  // Scaled from Neg 8: [1,2,2], k=3, wrong=3
  expect !CanPerform([1, 2, 2], 3, 3), "spec negative 6";

  // Scaled from Neg 10: [1,1,2], k=3, wrong=4
  expect !CanPerform([1, 1, 2], 3, 4), "spec negative 7";

  // ===== IMPLEMENTATION TESTS =====
  // Full-size test pairs (method is fast)

  // Test 1a
  var r1 := CopyPaste(2, 2, [1, 1]);
  expect r1 == 1, "impl test 1 failed";

  // Test 1b
  var r2 := CopyPaste(3, 5, [1, 2, 3]);
  expect r2 == 5, "impl test 2 failed";

  // Test 1c
  var r3 := CopyPaste(3, 7, [3, 2, 2]);
  expect r3 == 4, "impl test 3 failed";

  // Test 3
  var r4 := CopyPaste(2, 10, [1, 1]);
  expect r4 == 9, "impl test 4 failed";

  // Test 5
  var r5 := CopyPaste(4, 8, [2, 2, 2, 2]);
  expect r5 == 9, "impl test 5 failed";

  // Test 6
  var r6 := CopyPaste(2, 50, [1, 49]);
  expect r6 == 1, "impl test 6 failed";

  // Test 7
  var r7 := CopyPaste(5, 10, [1, 1, 1, 1, 1]);
  expect r7 == 36, "impl test 7 failed";

  // Test 8
  var r8 := CopyPaste(3, 7, [3, 2, 2]);
  expect r8 == 4, "impl test 8 failed";

  // Test 9
  var r9 := CopyPaste(2, 4, [2, 2]);
  expect r9 == 1, "impl test 9 failed";

  // Test 10
  var r10 := CopyPaste(6, 12, [1, 2, 3, 4, 5, 6]);
  expect r10 == 40, "impl test 10 failed";

  // Test 11a
  var r11 := CopyPaste(2, 3, [1, 2]);
  expect r11 == 1, "impl test 11 failed";

  // Test 11b
  var r12 := CopyPaste(3, 6, [1, 1, 1]);
  expect r12 == 10, "impl test 12 failed";

  print "All tests passed\n";
}