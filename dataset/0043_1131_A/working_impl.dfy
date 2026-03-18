method SeaBattle(w1: int, h1: int, w2: int, h2: int) returns (marked: int)
{
  marked := (w1 + 2) * (h1 + h2 + 2) - (w1 - w2) * h2 - w1 * h1 - w2 * h2;
}

method Main()
{
  var r: int;

  r := SeaBattle(2, 1, 2, 1);
  expect r == 12, "Test 1 failed";

  r := SeaBattle(2, 2, 1, 2);
  expect r == 16, "Test 2 failed";

  r := SeaBattle(1, 1, 1, 1);
  expect r == 10, "Test 3 failed";

  r := SeaBattle(1, 50, 1, 50);
  expect r == 206, "Test 4 failed";

  r := SeaBattle(6, 4, 2, 7);
  expect r == 38, "Test 5 failed";

  r := SeaBattle(100000000, 100000000, 99999999, 100000000);
  expect r == 600000004, "Test 6 failed";

  r := SeaBattle(100000000, 1, 100000000, 1);
  expect r == 200000008, "Test 7 failed";

  r := SeaBattle(19661988, 30021918, 8795449, 27534575);
  expect r == 154436966, "Test 8 failed";

  r := SeaBattle(98948781, 84140283, 95485812, 84557929);
  expect r == 535293990, "Test 9 failed";

  r := SeaBattle(47, 40, 42, 49);
  expect r == 276, "Test 10 failed";

  r := SeaBattle(18, 3, 8, 15);
  expect r == 76, "Test 11 failed";

  r := SeaBattle(49, 45, 49, 46);
  expect r == 284, "Test 12 failed";

  r := SeaBattle(50, 50, 50, 50);
  expect r == 304, "Test 13 failed";

  r := SeaBattle(24, 25, 16, 38);
  expect r == 178, "Test 14 failed";

  r := SeaBattle(23, 1, 12, 2);
  expect r == 56, "Test 15 failed";

  r := SeaBattle(1000000, 1000000, 1000000, 1000000);
  expect r == 6000004, "Test 16 failed";

  r := SeaBattle(1000000, 1000000, 999999, 1000000);
  expect r == 6000004, "Test 17 failed";

  r := SeaBattle(1000000, 1, 1000000, 1);
  expect r == 2000008, "Test 18 failed";

  r := SeaBattle(672810, 797124, 51792, 404095);
  expect r == 3748062, "Test 19 failed";

  r := SeaBattle(960051, 866743, 887923, 926936);
  expect r == 5507464, "Test 20 failed";

  print "All tests passed\n";
}