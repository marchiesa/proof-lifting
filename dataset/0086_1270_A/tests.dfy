// ── Spec helpers ──────────────────────────────────────────────────────

function SeqToSet(s: seq<int>): set<int>
  decreases |s|
{
  if |s| == 0 then {} else {s[|s|-1]} + SeqToSet(s[..|s|-1])
}

predicate NoDuplicates(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] != s[j]
}

predicate ValidDeck(n: int, a: seq<int>, b: seq<int>)
{
  n >= 2
  && |a| >= 1
  && |b| >= 1
  && NoDuplicates(a)
  && NoDuplicates(b)
  && SeqToSet(a) !! SeqToSet(b)
  && SeqToSet(a) + SeqToSet(b) == set i | 1 <= i <= n :: i
}

predicate Player1CanWin(S1: set<int>, S2: set<int>, steps: nat)
  decreases steps
{
  if S2 == {} then true
  else if S1 == {} || steps == 0 then false
  else exists c1 | c1 in S1 :: forall c2 | c2 in S2 ::
    if c1 > c2 then Player1CanWin(S1 + {c2}, S2 - {c2}, steps - 1)
    else Player1CanWin(S1 - {c1}, S2 + {c1}, steps - 1)
}

predicate Player1WinsGame(S1: set<int>, S2: set<int>, bound: nat)
{
  exists steps | 0 <= steps <= bound :: Player1CanWin(S1, S2, steps)
}

// ── Method with specification ─────────────────────────────────────────

method CardGame(n: int, k1: int, k2: int, a: seq<int>, b: seq<int>) returns (firstPlayerWins: bool)
  requires ValidDeck(n, a, b)
  requires k1 == |a| && k2 == |b|
  ensures firstPlayerWins <==> Player1WinsGame(SeqToSet(a), SeqToSet(b), n)
{
  var maxA := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] > maxA {
      maxA := a[i];
    }
    i := i + 1;
  }

  var maxB := b[0];
  var j := 1;
  while j < |b|
  {
    if b[j] > maxB {
      maxB := b[j];
    }
    j := j + 1;
  }

  firstPlayerWins := maxA > maxB;
}

method Main()
{
  // ═══════════════════════════════════════════════════════════════════
  // SPEC POSITIVE TESTS (small inputs, correct output matches spec)
  // ═══════════════════════════════════════════════════════════════════

  // From Test 1 TC1: n=2, a=[2], b=[1] → YES
  expect Player1WinsGame({2}, {1}, 2) == true, "spec positive 1";

  // From Test 2: n=2, a=[1], b=[2] → NO
  expect Player1WinsGame({1}, {2}, 2) == false, "spec positive 2";

  // From Test 3: n=3, a=[1,3], b=[2] → YES
  expect Player1WinsGame({1, 3}, {2}, 3) == true, "spec positive 3";

  // From Test 8 TC2: n=3, a=[3], b=[1,2] → YES
  expect Player1WinsGame({3}, {1, 2}, 3) == true, "spec positive 4";

  // From Test 4: n=4, a=[2,4], b=[1,3] → YES
  expect Player1WinsGame({2, 4}, {1, 3}, 4) == true, "spec positive 5";

  // From Test 8 TC3: n=4, a=[1,2,4], b=[3] → YES
  expect Player1WinsGame({1, 2, 4}, {3}, 4) == true, "spec positive 6";

  // ═══════════════════════════════════════════════════════════════════
  // SPEC NEGATIVE TESTS (small inputs, wrong output rejected by spec)
  // ═══════════════════════════════════════════════════════════════════

  // Neg 1 scaled (n=5→3): a={1,2}, b={3}, correct=NO, wrong=YES
  expect Player1WinsGame({1, 2}, {3}, 3) != true, "spec negative 1";

  // Neg 2: n=2, a={1}, b={2}, correct=NO, wrong=YES
  expect Player1WinsGame({1}, {2}, 2) != true, "spec negative 2";

  // Neg 3: n=3, a={1,3}, b={2}, correct=YES, wrong=NO
  expect Player1WinsGame({1, 3}, {2}, 3) != false, "spec negative 3";

  // Neg 4: n=4, a={2,4}, b={1,3}, correct=YES, wrong=NO
  expect Player1WinsGame({2, 4}, {1, 3}, 4) != false, "spec negative 4";

  // Neg 5 scaled (n=5→4): a={1,4}, b={2,3}, correct=YES, wrong=NO
  expect Player1WinsGame({1, 4}, {2, 3}, 4) != false, "spec negative 5";

  // Neg 8 game 3: n=4, a={1,2,4}, b={3}, correct=YES, wrong=NO
  expect Player1WinsGame({1, 2, 4}, {3}, 4) != false, "spec negative 6";

  // Neg 10 scaled (n=5→3): a={3}, b={1,2}, correct=YES, wrong=NO
  expect Player1WinsGame({3}, {1, 2}, 3) != false, "spec negative 7";

  // ═══════════════════════════════════════════════════════════════════
  // IMPLEMENTATION TESTS (full-size, call method and check output)
  // ═══════════════════════════════════════════════════════════════════

  // Test 1, TC1: n=2, a=[2], b=[1] → YES
  var r1 := CardGame(2, 1, 1, [2], [1]);
  expect r1 == true, "impl test 1.1 failed";

  // Test 1, TC2: n=5, a=[2,3], b=[1,4,5] → NO
  var r2 := CardGame(5, 2, 3, [2, 3], [1, 4, 5]);
  expect r2 == false, "impl test 1.2 failed";

  // Test 2: n=2, a=[1], b=[2] → NO
  var r3 := CardGame(2, 1, 1, [1], [2]);
  expect r3 == false, "impl test 2 failed";

  // Test 3: n=3, a=[1,3], b=[2] → YES
  var r4 := CardGame(3, 2, 1, [1, 3], [2]);
  expect r4 == true, "impl test 3 failed";

  // Test 4: n=4, a=[2,4], b=[1,3] → YES
  var r5 := CardGame(4, 2, 2, [2, 4], [1, 3]);
  expect r5 == true, "impl test 4 failed";

  // Test 5: n=5, a=[1,2,5], b=[3,4] → YES
  var r6 := CardGame(5, 3, 2, [1, 2, 5], [3, 4]);
  expect r6 == true, "impl test 5 failed";

  // Test 6: n=6, a=[6], b=[1,2,3,4,5] → YES
  var r7 := CardGame(6, 1, 5, [6], [1, 2, 3, 4, 5]);
  expect r7 == true, "impl test 6 failed";

  // Test 7: n=10, a=[2,4,6,8,10], b=[1,3,5,7,9] → YES
  var r8 := CardGame(10, 5, 5, [2, 4, 6, 8, 10], [1, 3, 5, 7, 9]);
  expect r8 == true, "impl test 7 failed";

  // Test 8, TC1: n=2, a=[2], b=[1] → YES
  var r9 := CardGame(2, 1, 1, [2], [1]);
  expect r9 == true, "impl test 8.1 failed";

  // Test 8, TC2: n=3, a=[3], b=[1,2] → YES
  var r10 := CardGame(3, 1, 2, [3], [1, 2]);
  expect r10 == true, "impl test 8.2 failed";

  // Test 8, TC3: n=4, a=[1,2,4], b=[3] → YES
  var r11 := CardGame(4, 3, 1, [1, 2, 4], [3]);
  expect r11 == true, "impl test 8.3 failed";

  // Test 9: n=7, a=[1,3,5,7], b=[2,4,6] → YES
  var r12 := CardGame(7, 4, 3, [1, 3, 5, 7], [2, 4, 6]);
  expect r12 == true, "impl test 9 failed";

  // Test 10, TC1: n=5, a=[2,3], b=[1,4,5] → NO
  var r13 := CardGame(5, 2, 3, [2, 3], [1, 4, 5]);
  expect r13 == false, "impl test 10.1 failed";

  // Test 10, TC2: n=5, a=[5], b=[1,2,3,4] → YES
  var r14 := CardGame(5, 1, 4, [5], [1, 2, 3, 4]);
  expect r14 == true, "impl test 10.2 failed";

  // Test 11: n=8, a=[1,4,8], b=[2,3,5,6,7] → YES
  var r15 := CardGame(8, 3, 5, [1, 4, 8], [2, 3, 5, 6, 7]);
  expect r15 == true, "impl test 11 failed";

  print "All tests passed\n";
}