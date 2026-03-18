// --- Specification ---

predicate ValidTime(h: int, m: int)
{
  0 <= h < 24 && 0 <= m < 60
}

function MinutesSinceMidnight(h: int, m: int): int
{
  h * 60 + m
}

function ClockStateAfter(h: int, m: int, n: int): int
{
  (MinutesSinceMidnight(h, m) + n) % 1440
}

predicate ReachesMidnight(h: int, m: int, n: int)
{
  ClockStateAfter(h, m, n) == 0
}

// --- Implementation ---

method MinutesBeforeNewYear(h: int, m: int) returns (minutes: int)
  requires ValidTime(h, m)
  ensures 1 <= minutes <= 1440
  ensures ReachesMidnight(h, m, minutes)
  ensures forall k | 1 <= k < minutes :: !ReachesMidnight(h, m, k)
{
  minutes := (23 - h) * 60 + (60 - m);
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // ReachesMidnight(h, m, correct_output) should hold

  // Test 1
  expect ReachesMidnight(23, 55, 5), "spec positive 1a";
  expect ReachesMidnight(23, 0, 60), "spec positive 1b";
  expect ReachesMidnight(0, 1, 1439), "spec positive 1c";
  expect ReachesMidnight(4, 20, 1180), "spec positive 1d";
  expect ReachesMidnight(23, 59, 1), "spec positive 1e";

  // Test 2
  expect ReachesMidnight(22, 30, 90), "spec positive 2a";
  expect ReachesMidnight(21, 10, 170), "spec positive 2b";
  expect ReachesMidnight(20, 21, 219), "spec positive 2c";
  expect ReachesMidnight(19, 59, 241), "spec positive 2d";

  // Test 3
  expect ReachesMidnight(1, 2, 1378), "spec positive 3";

  // Test 4
  expect ReachesMidnight(23, 55, 5), "spec positive 4";

  // Test 5
  expect ReachesMidnight(0, 1, 1439), "spec positive 5";

  // Test 6
  expect ReachesMidnight(12, 30, 690), "spec positive 6a";
  expect ReachesMidnight(6, 15, 1065), "spec positive 6b";
  expect ReachesMidnight(18, 45, 315), "spec positive 6c";

  // Test 7
  expect ReachesMidnight(23, 59, 1), "spec positive 7a";
  expect ReachesMidnight(1, 0, 1380), "spec positive 7b";

  // Test 8
  expect ReachesMidnight(0, 30, 1410), "spec positive 8a";
  expect ReachesMidnight(3, 10, 1250), "spec positive 8b";
  expect ReachesMidnight(20, 5, 235), "spec positive 8c";
  expect ReachesMidnight(11, 11, 769), "spec positive 8d";

  // Test 9
  expect ReachesMidnight(12, 0, 720), "spec positive 9";

  // Test 10
  expect ReachesMidnight(1, 1, 1379), "spec positive 10a";
  expect ReachesMidnight(2, 2, 1318), "spec positive 10b";
  expect ReachesMidnight(3, 3, 1257), "spec positive 10c";
  expect ReachesMidnight(4, 4, 1196), "spec positive 10d";
  expect ReachesMidnight(5, 5, 1135), "spec positive 10e";

  // ===== SPEC NEGATIVE TESTS =====
  // ReachesMidnight(h, m, wrong_output) should NOT hold

  // Negative 1: (23,55) wrong 6, correct 5
  expect !ReachesMidnight(23, 55, 6), "spec negative 1";

  // Negative 2: (23,55) wrong 6, correct 5
  expect !ReachesMidnight(23, 55, 6), "spec negative 2";

  // Negative 3: (1,2) wrong 1379, correct 1378
  expect !ReachesMidnight(1, 2, 1379), "spec negative 3";

  // Negative 4: (23,55) wrong 6, correct 5
  expect !ReachesMidnight(23, 55, 6), "spec negative 4";

  // Negative 5: (0,1) wrong 1440, correct 1439
  expect !ReachesMidnight(0, 1, 1440), "spec negative 5";

  // Negative 6: (12,30) wrong 691, correct 690
  expect !ReachesMidnight(12, 30, 691), "spec negative 6";

  // Negative 7: (23,59) wrong 2, correct 1
  expect !ReachesMidnight(23, 59, 2), "spec negative 7";

  // Negative 8: (0,30) wrong 1411, correct 1410
  expect !ReachesMidnight(0, 30, 1411), "spec negative 8";

  // Negative 9: (12,0) wrong 721, correct 720
  expect !ReachesMidnight(12, 0, 721), "spec negative 9";

  // Negative 10: (1,1) wrong 1380, correct 1379
  expect !ReachesMidnight(1, 1, 1380), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  var result: int;

  // Test 1
  result := MinutesBeforeNewYear(23, 55);
  expect result == 5, "impl test 1a";
  result := MinutesBeforeNewYear(23, 0);
  expect result == 60, "impl test 1b";
  result := MinutesBeforeNewYear(0, 1);
  expect result == 1439, "impl test 1c";
  result := MinutesBeforeNewYear(4, 20);
  expect result == 1180, "impl test 1d";
  result := MinutesBeforeNewYear(23, 59);
  expect result == 1, "impl test 1e";

  // Test 2
  result := MinutesBeforeNewYear(22, 30);
  expect result == 90, "impl test 2a";
  result := MinutesBeforeNewYear(21, 10);
  expect result == 170, "impl test 2b";
  result := MinutesBeforeNewYear(20, 21);
  expect result == 219, "impl test 2c";
  result := MinutesBeforeNewYear(19, 59);
  expect result == 241, "impl test 2d";

  // Test 3
  result := MinutesBeforeNewYear(1, 2);
  expect result == 1378, "impl test 3";

  // Test 4
  result := MinutesBeforeNewYear(23, 55);
  expect result == 5, "impl test 4";

  // Test 5
  result := MinutesBeforeNewYear(0, 1);
  expect result == 1439, "impl test 5";

  // Test 6
  result := MinutesBeforeNewYear(12, 30);
  expect result == 690, "impl test 6a";
  result := MinutesBeforeNewYear(6, 15);
  expect result == 1065, "impl test 6b";
  result := MinutesBeforeNewYear(18, 45);
  expect result == 315, "impl test 6c";

  // Test 7
  result := MinutesBeforeNewYear(23, 59);
  expect result == 1, "impl test 7a";
  result := MinutesBeforeNewYear(1, 0);
  expect result == 1380, "impl test 7b";

  // Test 8
  result := MinutesBeforeNewYear(0, 30);
  expect result == 1410, "impl test 8a";
  result := MinutesBeforeNewYear(3, 10);
  expect result == 1250, "impl test 8b";
  result := MinutesBeforeNewYear(20, 5);
  expect result == 235, "impl test 8c";
  result := MinutesBeforeNewYear(11, 11);
  expect result == 769, "impl test 8d";

  // Test 9
  result := MinutesBeforeNewYear(12, 0);
  expect result == 720, "impl test 9";

  // Test 10
  result := MinutesBeforeNewYear(1, 1);
  expect result == 1379, "impl test 10a";
  result := MinutesBeforeNewYear(2, 2);
  expect result == 1318, "impl test 10b";
  result := MinutesBeforeNewYear(3, 3);
  expect result == 1257, "impl test 10c";
  result := MinutesBeforeNewYear(4, 4);
  expect result == 1196, "impl test 10d";
  result := MinutesBeforeNewYear(5, 5);
  expect result == 1135, "impl test 10e";

  print "All tests passed\n";
}