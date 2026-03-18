// --- Formal specification predicates ---

predicate IsDigit(c: char)
{
  '0' <= c <= '9'
}

predicate IsPhoneNumber(t: seq<char>)
{
  |t| == 11 && t[0] == '8' && (forall i | 0 <= i < |t| :: IsDigit(t[i]))
}

predicate IsSubsequence(sub: seq<char>, s: seq<char>)
  decreases |s|
{
  if |sub| == 0 then true
  else if |s| == 0 then false
  else
    (sub[0] == s[0] && IsSubsequence(sub[1..], s[1..]))
    || IsSubsequence(sub, s[1..])
}

predicate CanFormPhone(s: seq<char>, remaining: nat)
  decreases |s|
{
  if remaining == 0 then true
  else if |s| == 0 then false
  else
    CanFormPhone(s[1..], remaining)
    ||
    (IsDigit(s[0]) && (remaining == 11 ==> s[0] == '8') && CanFormPhone(s[1..], remaining - 1))
}

// --- Method with specification ---

method TelephoneNumber(s: string, n: int) returns (result: bool)
  requires n == |s|
  requires forall i | 0 <= i < n :: IsDigit(s[i])
  ensures result == CanFormPhone(s, 11)
{
  var i := 0;
  while i < n - 10
  {
    if s[i] == '8' {
      return true;
    }
    i := i + 1;
  }
  return false;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // ensures: result == CanFormPhone(s, 11)
  // Check that CanFormPhone agrees with the correct output for each test case.

  // Positive pair 1, case 1: s="7818005553535" → true
  expect CanFormPhone("7818005553535", 11) == true, "spec positive 1";

  // Positive pair 1, case 2: s="31415926535" → false
  expect CanFormPhone("31415926535", 11) == false, "spec positive 2";

  // Positive pair 2: s="80000000000" → true
  expect CanFormPhone("80000000000", 11) == true, "spec positive 3";

  // Positive pair 3: s="83583640644" → true
  expect CanFormPhone("83583640644", 11) == true, "spec positive 4";

  // Additional scaled-down spec positive tests
  expect CanFormPhone("88888888888", 11) == true, "spec positive 5";
  expect CanFormPhone("81234567890", 11) == true, "spec positive 6";
  expect CanFormPhone("00000000000", 11) == false, "spec positive 7";

  // === SPEC NEGATIVE TESTS ===
  // Check that CanFormPhone rejects the WRONG output for each test case.

  // Negative pair 1, case 2: s="31415926535", correct=false, wrong=true
  expect !(CanFormPhone("31415926535", 11) == true), "spec negative 1";

  // Negative pair 2: s="80000000000", correct=true, wrong=false
  expect !(CanFormPhone("80000000000", 11) == false), "spec negative 2";

  // Negative pair 3: s="83583640644", correct=true, wrong=false
  expect !(CanFormPhone("83583640644", 11) == false), "spec negative 3";

  // Additional spec negative tests
  expect !(CanFormPhone("88888888888", 11) == false), "spec negative 4";
  expect !(CanFormPhone("12345678901", 11) == true), "spec negative 5";
  expect !(CanFormPhone("00000000000", 11) == true), "spec negative 6";
  expect !(CanFormPhone("18888888888", 11) == true), "spec negative 7";

  // === IMPLEMENTATION TESTS ===

  // Test pair 1, case 1: n=13, s="7818005553535" → true
  var r1 := TelephoneNumber("7818005553535", 13);
  expect r1 == true, "impl test 1 failed";

  // Test pair 1, case 2: n=11, s="31415926535" → false
  var r2 := TelephoneNumber("31415926535", 11);
  expect r2 == false, "impl test 2 failed";

  // Test pair 2: n=11, s="80000000000" → true
  var r3 := TelephoneNumber("80000000000", 11);
  expect r3 == true, "impl test 3 failed";

  // Test pair 3: n=11, s="83583640644" → true
  var r4 := TelephoneNumber("83583640644", 11);
  expect r4 == true, "impl test 4 failed";

  print "All tests passed\n";
}