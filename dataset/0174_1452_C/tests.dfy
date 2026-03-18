// --- Specification: model the problem's structure ---

function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

function ExtractByMask(s: seq<char>, mask: nat): seq<char>
  decreases |s|
{
  if |s| == 0 then []
  else if mask % 2 == 1 then [s[0]] + ExtractByMask(s[1..], mask / 2)
  else ExtractByMask(s[1..], mask / 2)
}

function RemoveByMask(s: seq<char>, mask: nat): seq<char>
  decreases |s|
{
  if |s| == 0 then []
  else if mask % 2 == 1 then RemoveByMask(s[1..], mask / 2)
  else [s[0]] + RemoveByMask(s[1..], mask / 2)
}

function CheckRBSWithStack(s: seq<char>, stack: seq<char>): bool
  decreases |s|
{
  if |s| == 0 then |stack| == 0
  else
    var c := s[0];
    if c == '(' || c == '[' then
      CheckRBSWithStack(s[1..], stack + [c])
    else if c == ')' then
      |stack| > 0 && stack[|stack|-1] == '(' && CheckRBSWithStack(s[1..], stack[..|stack|-1])
    else if c == ']' then
      |stack| > 0 && stack[|stack|-1] == '[' && CheckRBSWithStack(s[1..], stack[..|stack|-1])
    else
      false
}

predicate IsRBS(s: seq<char>) {
  CheckRBSWithStack(s, [])
}

predicate CanAchieveKMoves(s: seq<char>, k: nat)
  decreases k
{
  if k == 0 then true
  else
    exists mask | 1 <= mask < Pow2(|s|) ::
      IsRBS(ExtractByMask(s, mask)) &&
      CanAchieveKMoves(RemoveByMask(s, mask), k - 1)
}

// --- Method with formal specification ---

method TwoBrackets(s: string) returns (moves: int)
  ensures moves >= 0
  ensures CanAchieveKMoves(s, moves)
  ensures forall k | moves < k <= |s| / 2 :: !CanAchieveKMoves(s, k)
{
  var openCount := new int[2];
  openCount[0] := 0;
  openCount[1] := 0;
  moves := 0;
  var j := 0;
  while j < |s|
  {
    var c := s[j];
    var i := if c == '[' || c == ']' then 1 else 0;
    if c == '(' || c == '[' {
      openCount[i] := openCount[i] + 1;
    } else if openCount[i] > 0 {
      openCount[i] := openCount[i] - 1;
      moves := moves + 1;
    }
    j := j + 1;
  }
}

method Main()
{
  // ============================================================
  // SPEC POSITIVE tests: ensures predicates hold on correct outputs
  // ============================================================

  // From Test 1.1: "()" -> 1
  expect CanAchieveKMoves("()", 1), "spec positive 1";
  // |s|/2=1, moves=1, forall range empty

  // From Test 2.2/2.3: "[]" -> 1
  expect CanAchieveKMoves("[]", 1), "spec positive 2";

  // From Test 1.4: ")]([" -> 0
  expect CanAchieveKMoves(")]([", 0), "spec positive 3";
  // forall: 0 < k <= 2
  expect !CanAchieveKMoves(")]([", 1), "spec positive 3 forall k=1";
  expect !CanAchieveKMoves(")]([", 2), "spec positive 3 forall k=2";

  // From Test 1.5: ")[(]" -> 1
  expect CanAchieveKMoves(")[(]", 1), "spec positive 4";
  // forall: 1 < k <= 2
  expect !CanAchieveKMoves(")[(]", 2), "spec positive 4 forall k=2";

  // From Test 2.1: "[()]" -> 2
  expect CanAchieveKMoves("[()]", 2), "spec positive 5";
  // |s|/2=2, moves=2, forall range empty

  // From Test 1.2: "[]()" -> 2
  expect CanAchieveKMoves("[]()", 2), "spec positive 6";

  // From Test 1.3: "([)]" -> 2
  expect CanAchieveKMoves("([)]", 2), "spec positive 7";

  // ============================================================
  // SPEC NEGATIVE tests: ensures predicates REJECT wrong outputs
  // ============================================================

  // Negative 1: "()" -> wrong: 2 (correct: 1)
  expect !CanAchieveKMoves("()", 2), "spec negative 1";

  // Negative 2: "[()]" -> wrong: 3 (correct: 2)
  expect !CanAchieveKMoves("[()]", 3), "spec negative 2";

  // Negative 3: "()" -> wrong: 2 (correct: 1)
  expect !CanAchieveKMoves("()", 2), "spec negative 3";

  // Negative 4: "()" -> wrong: 2 (correct: 1)
  expect !CanAchieveKMoves("()", 2), "spec negative 4";

  // Derived: "[]" -> wrong: 2 (correct: 1)
  expect !CanAchieveKMoves("[]", 2), "spec negative 5";

  // Derived: ")[(]" -> wrong: 2 (correct: 1)
  expect !CanAchieveKMoves(")[(]", 2), "spec negative 6";

  // Derived: "([)]" -> wrong: 3 (correct: 2)
  expect !CanAchieveKMoves("([)]", 3), "spec negative 7";

  // ============================================================
  // IMPLEMENTATION tests: call TwoBrackets and check results
  // ============================================================

  // Test 1
  var r1 := TwoBrackets("()");
  expect r1 == 1, "impl test 1.1 failed";

  var r2 := TwoBrackets("[]()");
  expect r2 == 2, "impl test 1.2 failed";

  var r3 := TwoBrackets("([)]");
  expect r3 == 2, "impl test 1.3 failed";

  var r4 := TwoBrackets(")]([");
  expect r4 == 0, "impl test 1.4 failed";

  var r5 := TwoBrackets(")[(]");
  expect r5 == 1, "impl test 1.5 failed";

  // Test 2
  var r6 := TwoBrackets("[()]");
  expect r6 == 2, "impl test 2.1 failed";

  var r7 := TwoBrackets("[]");
  expect r7 == 1, "impl test 2.2 failed";

  var r8 := TwoBrackets("[]");
  expect r8 == 1, "impl test 2.3 failed";

  var r9 := TwoBrackets("()");
  expect r9 == 1, "impl test 2.4 failed";

  // Test 3
  var r10 := TwoBrackets("()");
  expect r10 == 1, "impl test 3.1 failed";

  var r11 := TwoBrackets("()");
  expect r11 == 1, "impl test 3.2 failed";

  var r12 := TwoBrackets("()");
  expect r12 == 1, "impl test 3.3 failed";

  var r13 := TwoBrackets("()");
  expect r13 == 1, "impl test 3.4 failed";

  // Test 4
  var r14 := TwoBrackets("()");
  expect r14 == 1, "impl test 4.1 failed";

  var r15 := TwoBrackets("()");
  expect r15 == 1, "impl test 4.2 failed";

  var r16 := TwoBrackets("()");
  expect r16 == 1, "impl test 4.3 failed";

  var r17 := TwoBrackets("()");
  expect r17 == 1, "impl test 4.4 failed";

  var r18 := TwoBrackets("()");
  expect r18 == 1, "impl test 4.5 failed";

  var r19 := TwoBrackets("()");
  expect r19 == 1, "impl test 4.6 failed";

  var r20 := TwoBrackets("()");
  expect r20 == 1, "impl test 4.7 failed";

  print "All tests passed\n";
}