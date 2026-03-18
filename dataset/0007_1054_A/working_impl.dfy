method ElevatorOrStairs(x: int, y: int, z: int, t1: int, t2: int, t3: int) returns (result: string)
{
  var dxy := if x >= y then x - y else y - x;
  var dxz := if x >= z then x - z else z - x;
  if t1 * dxy >= t2 * dxy + t2 * dxz + t3 * 3 {
    result := "YES";
  } else {
    result := "NO";
  }
}

method Main()
{
  var r: string;

  r := ElevatorOrStairs(5, 1, 4, 4, 2, 1);
  expect r == "YES", "Test 1 failed";

  r := ElevatorOrStairs(1, 6, 6, 2, 1, 1);
  expect r == "NO", "Test 2 failed";

  r := ElevatorOrStairs(4, 1, 7, 4, 1, 2);
  expect r == "YES", "Test 3 failed";

  r := ElevatorOrStairs(749, 864, 931, 266, 94, 891);
  expect r == "NO", "Test 4 failed";

  r := ElevatorOrStairs(719, 137, 307, 244, 724, 777);
  expect r == "NO", "Test 5 failed";

  r := ElevatorOrStairs(608, 11, 980, 338, 208, 78);
  expect r == "YES", "Test 6 failed";

  r := ElevatorOrStairs(571, 695, 153, 288, 64, 421);
  expect r == "NO", "Test 7 failed";

  r := ElevatorOrStairs(837, 544, 703, 808, 549, 694);
  expect r == "YES", "Test 8 failed";

  r := ElevatorOrStairs(271, 634, 606, 95, 39, 523);
  expect r == "YES", "Test 9 failed";

  r := ElevatorOrStairs(1000, 999, 1000, 1000, 1000, 1000);
  expect r == "NO", "Test 10 failed";

  r := ElevatorOrStairs(236, 250, 259, 597, 178, 591);
  expect r == "NO", "Test 11 failed";

  r := ElevatorOrStairs(385, 943, 507, 478, 389, 735);
  expect r == "NO", "Test 12 failed";

  r := ElevatorOrStairs(559, 540, 735, 635, 58, 252);
  expect r == "NO", "Test 13 failed";

  r := ElevatorOrStairs(500, 922, 443, 965, 850, 27);
  expect r == "NO", "Test 14 failed";

  r := ElevatorOrStairs(995, 584, 903, 362, 290, 971);
  expect r == "NO", "Test 15 failed";

  r := ElevatorOrStairs(494, 475, 456, 962, 297, 450);
  expect r == "NO", "Test 16 failed";

  r := ElevatorOrStairs(866, 870, 898, 979, 30, 945);
  expect r == "YES", "Test 17 failed";

  r := ElevatorOrStairs(602, 375, 551, 580, 466, 704);
  expect r == "YES", "Test 18 failed";

  r := ElevatorOrStairs(76, 499, 93, 623, 595, 576);
  expect r == "YES", "Test 19 failed";

  r := ElevatorOrStairs(256, 45, 584, 731, 281, 927);
  expect r == "YES", "Test 20 failed";

  print "All tests passed\n";
}