method MinutesBeforeNewYear(h: int, m: int) returns (minutes: int)
{
  minutes := (23 - h) * 60 + (60 - m);
}

method Main()
{
  var result: int;

  // Test 1
  result := MinutesBeforeNewYear(23, 55);
  expect result == 5, "Expected 5 for (23, 55)";
  result := MinutesBeforeNewYear(23, 0);
  expect result == 60, "Expected 60 for (23, 0)";
  result := MinutesBeforeNewYear(0, 1);
  expect result == 1439, "Expected 1439 for (0, 1)";
  result := MinutesBeforeNewYear(4, 20);
  expect result == 1180, "Expected 1180 for (4, 20)";
  result := MinutesBeforeNewYear(23, 59);
  expect result == 1, "Expected 1 for (23, 59)";

  // Test 2
  result := MinutesBeforeNewYear(22, 30);
  expect result == 90, "Expected 90 for (22, 30)";
  result := MinutesBeforeNewYear(21, 10);
  expect result == 170, "Expected 170 for (21, 10)";
  result := MinutesBeforeNewYear(20, 21);
  expect result == 219, "Expected 219 for (20, 21)";
  result := MinutesBeforeNewYear(19, 59);
  expect result == 241, "Expected 241 for (19, 59)";

  // Test 3
  result := MinutesBeforeNewYear(1, 2);
  expect result == 1378, "Expected 1378 for (1, 2)";

  // Test 6
  result := MinutesBeforeNewYear(12, 30);
  expect result == 690, "Expected 690 for (12, 30)";
  result := MinutesBeforeNewYear(6, 15);
  expect result == 1065, "Expected 1065 for (6, 15)";
  result := MinutesBeforeNewYear(18, 45);
  expect result == 315, "Expected 315 for (18, 45)";

  // Test 7
  result := MinutesBeforeNewYear(1, 0);
  expect result == 1380, "Expected 1380 for (1, 0)";

  // Test 8
  result := MinutesBeforeNewYear(0, 30);
  expect result == 1410, "Expected 1410 for (0, 30)";
  result := MinutesBeforeNewYear(3, 10);
  expect result == 1250, "Expected 1250 for (3, 10)";
  result := MinutesBeforeNewYear(20, 5);
  expect result == 235, "Expected 235 for (20, 5)";
  result := MinutesBeforeNewYear(11, 11);
  expect result == 769, "Expected 769 for (11, 11)";

  // Test 9
  result := MinutesBeforeNewYear(12, 0);
  expect result == 720, "Expected 720 for (12, 0)";

  // Test 10
  result := MinutesBeforeNewYear(1, 1);
  expect result == 1379, "Expected 1379 for (1, 1)";
  result := MinutesBeforeNewYear(2, 2);
  expect result == 1318, "Expected 1318 for (2, 2)";
  result := MinutesBeforeNewYear(3, 3);
  expect result == 1257, "Expected 1257 for (3, 3)";
  result := MinutesBeforeNewYear(4, 4);
  expect result == 1196, "Expected 1196 for (4, 4)";
  result := MinutesBeforeNewYear(5, 5);
  expect result == 1135, "Expected 1135 for (5, 5)";

  // Test 11
  result := MinutesBeforeNewYear(0, 59);
  expect result == 1381, "Expected 1381 for (0, 59)";
  result := MinutesBeforeNewYear(23, 1);
  expect result == 59, "Expected 59 for (23, 1)";

  // Test 12
  result := MinutesBeforeNewYear(7, 7);
  expect result == 1013, "Expected 1013 for (7, 7)";
  result := MinutesBeforeNewYear(14, 14);
  expect result == 586, "Expected 586 for (14, 14)";
  result := MinutesBeforeNewYear(21, 21);
  expect result == 159, "Expected 159 for (21, 21)";

  // Test 13
  result := MinutesBeforeNewYear(10, 10);
  expect result == 830, "Expected 830 for (10, 10)";
  result := MinutesBeforeNewYear(20, 20);
  expect result == 220, "Expected 220 for (20, 20)";
  result := MinutesBeforeNewYear(15, 45);
  expect result == 495, "Expected 495 for (15, 45)";
  result := MinutesBeforeNewYear(8, 30);
  expect result == 930, "Expected 930 for (8, 30)";
  result := MinutesBeforeNewYear(0, 15);
  expect result == 1425, "Expected 1425 for (0, 15)";
  result := MinutesBeforeNewYear(22, 0);
  expect result == 120, "Expected 120 for (22, 0)";

  print "All tests passed\n";
}