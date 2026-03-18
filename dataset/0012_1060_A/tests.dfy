function CountOccurrences(s: seq<int>, v: int): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[|s|-1] == v then 1 else 0) + CountOccurrences(s[..|s|-1], v)
}

predicate ValidPhoneAssignment(assignment: seq<int>, k: int, digits: seq<int>)
{
  |assignment| == |digits| &&
  k >= 0 &&
  (forall i | 0 <= i < |assignment| :: 0 <= assignment[i] <= k) &&
  (forall j | 1 <= j <= k ::
    CountOccurrences(assignment, j) == 11 &&
    (exists i | 0 <= i < |digits| :: assignment[i] == j && digits[i] == 8))
}

predicate Achievable(k: int, digits: seq<int>)
{
  k >= 0 && 11 * k <= |digits| && k <= CountOccurrences(digits, 8)
}

method PhoneNumbers(n: int, digits: seq<int>) returns (count: int)
  requires n == |digits|
  ensures Achievable(count, digits)
  ensures !Achievable(count + 1, digits)
{
  var cnt8 := 0;
  for i := 0 to |digits| {
    if digits[i] == 8 {
      cnt8 := cnt8 + 1;
    }
  }
  if cnt8 < n / 11 {
    count := cnt8;
  } else {
    count := n / 11;
  }
}

method Main()
{
  var r: int;

  // ===== SPEC POSITIVE TESTS =====
  // For each, test both ensures: Achievable(correct, digits) and !Achievable(correct+1, digits)

  // SP1: correct=1 (from test 1, length 11)
  expect Achievable(1, [0,0,0,0,0,0,0,0,0,0,8]), "spec positive 1a";
  expect !Achievable(2, [0,0,0,0,0,0,0,0,0,0,8]), "spec positive 1b";

  // SP2: correct=2 (from test 2, length 22)
  expect Achievable(2, [0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,8,8]), "spec positive 2a";
  expect !Achievable(3, [0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,8,8]), "spec positive 2b";

  // SP3: correct=0, no 8s (from test 3, scaled to length 3)
  expect Achievable(0, [3,1,4]), "spec positive 3a";
  expect !Achievable(1, [3,1,4]), "spec positive 3b";

  // SP4: correct=0, no 8s (from test 6, scaled to length 3)
  expect Achievable(0, [5,0,9]), "spec positive 4a";
  expect !Achievable(1, [5,0,9]), "spec positive 4b";

  // SP5: correct=1 (from test 7, scaled: length 11, one 8)
  expect Achievable(1, [1,9,7,6,4,7,3,6,2,1,8]), "spec positive 5a";
  expect !Achievable(2, [1,9,7,6,4,7,3,6,2,1,8]), "spec positive 5b";

  // SP6: correct=0, all 8s but too short (from test 9, scaled to length 3)
  expect Achievable(0, [8,8,8]), "spec positive 6a";
  expect !Achievable(1, [8,8,8]), "spec positive 6b";

  // SP7: correct=1, all 8s length 20 (from test 10)
  expect Achievable(1, [8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8]), "spec positive 7a";
  expect !Achievable(2, [8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8]), "spec positive 7b";

  // SP8: correct=1, all 8s length 11 (from test 10 scaled)
  expect Achievable(1, [8,8,8,8,8,8,8,8,8,8,8]), "spec positive 8a";
  expect !Achievable(2, [8,8,8,8,8,8,8,8,8,8,8]), "spec positive 8b";

  // SP9: correct=0, no 8s (from test 18, scaled to length 3)
  expect Achievable(0, [2,4,5]), "spec positive 9a";
  expect !Achievable(1, [2,4,5]), "spec positive 9b";

  // SP10: correct=2 (from test 20, scaled: length 22, many 8s)
  expect Achievable(2, [0,8,8,8,8,8,8,8,8,8,3,4,3,8,8,1,8,8,8,8,8,0]), "spec positive 10a";
  expect !Achievable(3, [0,8,8,8,8,8,8,8,8,8,3,4,3,8,8,1,8,8,8,8,8,0]), "spec positive 10b";

  // ===== SPEC NEGATIVE TESTS =====
  // Test that Achievable(wrong_output, digits) is false

  // SN1: wrong=2, correct=1 (from neg 1, length 11)
  expect !Achievable(2, [0,0,0,0,0,0,0,0,0,0,8]), "spec negative 1";

  // SN2: wrong=3, correct=2 (from neg 2, length 22)
  expect !Achievable(3, [0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,8,8]), "spec negative 2";

  // SN3: wrong=1, correct=0, no 8s (from neg 3, scaled to length 3)
  expect !Achievable(1, [3,1,4]), "spec negative 3";

  // SN4: wrong=1, correct=0, no 8s (from neg 6, scaled to length 3)
  expect !Achievable(1, [5,0,9]), "spec negative 4";

  // SN5: wrong=2, correct=1 (from neg 7, scaled: length 11, one 8)
  expect !Achievable(2, [1,9,7,6,4,7,3,6,2,1,8]), "spec negative 5";

  // SN6: wrong=1, correct=0, all 8s but too short (from neg 9, scaled to length 3)
  expect !Achievable(1, [8,8,8]), "spec negative 6";

  // SN7: wrong=2, correct=1, all 8s length 20 (from neg 10)
  expect !Achievable(2, [8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8]), "spec negative 7";

  // SN8: wrong=2, correct=1, all 8s length 11 (scaled from neg 8/10)
  expect !Achievable(2, [8,8,8,8,8,8,8,8,8,8,8]), "spec negative 8";

  // SN9: wrong=1, correct=0, no 8s (from neg 3 variant)
  expect !Achievable(1, [2,4,5]), "spec negative 9";

  // SN10: wrong=3, correct=2 (from neg 2 variant, length 22)
  expect !Achievable(3, [0,8,8,8,8,8,8,8,8,8,3,4,3,8,8,1,8,8,8,8,8,0]), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====

  // Test 1
  r := PhoneNumbers(11, [0,0,0,0,0,0,0,0,0,0,8]);
  expect r == 1, "impl test 1 failed";

  // Test 2
  r := PhoneNumbers(22, [0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,8,8]);
  expect r == 2, "impl test 2 failed";

  // Test 3
  r := PhoneNumbers(11, [3,1,4,1,5,9,2,6,5,3,5]);
  expect r == 0, "impl test 3 failed";

  // Test 4
  r := PhoneNumbers(99, [0,9,7,1,6,7,8,1,5,5,2,7,6,6,3,5,4,4,9,0,5,7,8,2,5,7,4,8,1,7,3,1,4,1,3,9,3,1,1,0,6,7,3,2,8,5,3,3,9,7,0,6,6,3,8,7,3,7,1,8,4,5,0,5,4,5,4,6,7,4,5,0,0,5,9,0,5,9,8,6,9,6,1,8,2,1,1,3,6,1,4,6,9,5,0,5,1,0,8]);
  expect r == 9, "impl test 4 failed";

  // Test 5
  r := PhoneNumbers(100, [8,8,2,0,2,8,6,2,8,5,1,8,5,2,4,4,9,3,8,4,5,2,4,8,8,8,8,7,0,8,8,8,7,1,4,5,7,0,9,8,9,4,5,8,7,4,4,8,6,9,8,8,6,9,8,4,6,8,7,8,8,3,8,1,4,1,7,3,3,2,8,4,2,8,8,8,9,2,8,1,8,8,6,8,8,8,8,7,6,4,1,1,3,2,1,9,4,9,5,6]);
  expect r == 9, "impl test 5 failed";

  // Test 6
  r := PhoneNumbers(99, [5,0,9,1,7,0,3,3,2,5,2,3,5,0,2,5,6,5,7,5,5,6,5,0,0,4,7,9,4,2,9,1,4,7,4,7,1,2,0,1,0,2,2,4,0,3,9,6,2,4,5,4,5,3,4,0,6,7,9,0,2,7,2,7,9,3,9,9,6,9,1,3,9,0,5,0,6,0,4,5,0,4,1,4,2,5,5,6,1,6,7,9,1,7,0,4,3,2,0]);
  expect r == 0, "impl test 6 failed";

  // Test 7
  r := PhoneNumbers(100, [1,9,7,6,4,7,3,6,2,1,5,6,9,9,0,3,1,7,2,7,2,1,4,0,7,7,6,3,7,3,7,1,7,9,6,3,9,0,5,5,5,6,1,7,4,6,3,1,0,3,6,9,7,7,9,1,6,7,3,5,1,4,1,9,7,1,3,9,1,6,1,6,0,7,0,0,0,9,6,1,7,3,6,2,2,4,2,7,0,7,7,7,5,7,9,8,6,0,2,6]);
  expect r == 1, "impl test 7 failed";

  // Test 8
  r := PhoneNumbers(100, [8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8]);
  expect r == 9, "impl test 8 failed";

  // Test 9
  r := PhoneNumbers(10, [8,8,8,8,8,8,8,8,8,8]);
  expect r == 0, "impl test 9 failed";

  // Test 10
  r := PhoneNumbers(20, [8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8]);
  expect r == 1, "impl test 10 failed";

  // Test 11
  r := PhoneNumbers(30, [8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8]);
  expect r == 2, "impl test 11 failed";

  // Test 12
  r := PhoneNumbers(40, [8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8]);
  expect r == 3, "impl test 12 failed";

  // Test 13
  r := PhoneNumbers(50, [8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8]);
  expect r == 4, "impl test 13 failed";

  // Test 14
  r := PhoneNumbers(60, [8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8]);
  expect r == 5, "impl test 14 failed";

  // Test 15
  r := PhoneNumbers(70, [8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8]);
  expect r == 6, "impl test 15 failed";

  // Test 16
  r := PhoneNumbers(80, [8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8]);
  expect r == 7, "impl test 16 failed";

  // Test 17
  r := PhoneNumbers(90, [8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8]);
  expect r == 8, "impl test 17 failed";

  // Test 18
  r := PhoneNumbers(11, [2,4,5,7,2,3,6,6,3,9,0]);
  expect r == 0, "impl test 18 failed";

  // Test 19
  r := PhoneNumbers(21, [5,8,2,5,8,6,7,8,8,2,8,9,4,8,4,8,7,8,5,8,8]);
  expect r == 1, "impl test 19 failed";

  // Test 20
  r := PhoneNumbers(31, [0,8,6,8,8,8,9,8,8,8,3,4,3,8,8,1,8,8,8,9,8,7,8,8,8,8,3,8,8,0,8]);
  expect r == 2, "impl test 20 failed";

  print "All tests passed\n";
}