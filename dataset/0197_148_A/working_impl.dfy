method InsomniaCure(k: int, l: int, m: int, n: int, d: int) returns (count: int)
{
  count := 0;
  var i := 1;
  while i <= d
  {
    if i % k == 0 || i % l == 0 || i % m == 0 || i % n == 0 {
      count := count + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  var result: int;

  result := InsomniaCure(1, 2, 3, 4, 12);
  expect result == 12, "Test 1 failed";

  result := InsomniaCure(2, 3, 4, 5, 24);
  expect result == 17, "Test 2 failed";

  result := InsomniaCure(1, 1, 1, 1, 100000);
  expect result == 100000, "Test 3 failed";

  result := InsomniaCure(10, 9, 8, 7, 6);
  expect result == 0, "Test 4 failed";

  result := InsomniaCure(8, 4, 4, 3, 65437);
  expect result == 32718, "Test 5 failed";

  result := InsomniaCure(8, 4, 1, 10, 59392);
  expect result == 59392, "Test 6 failed";

  result := InsomniaCure(4, 1, 8, 7, 44835);
  expect result == 44835, "Test 7 failed";

  result := InsomniaCure(6, 1, 7, 2, 62982);
  expect result == 62982, "Test 8 failed";

  result := InsomniaCure(2, 7, 4, 9, 56937);
  expect result == 35246, "Test 9 failed";

  result := InsomniaCure(2, 9, 8, 1, 75083);
  expect result == 75083, "Test 10 failed";

  result := InsomniaCure(8, 7, 7, 6, 69038);
  expect result == 24656, "Test 11 failed";

  result := InsomniaCure(4, 4, 2, 3, 54481);
  expect result == 36320, "Test 12 failed";

  result := InsomniaCure(6, 4, 9, 8, 72628);
  expect result == 28244, "Test 13 failed";

  result := InsomniaCure(9, 7, 8, 10, 42357);
  expect result == 16540, "Test 14 failed";

  result := InsomniaCure(5, 6, 4, 3, 60504);
  expect result == 36302, "Test 15 failed";

  result := InsomniaCure(7, 2, 3, 8, 21754);
  expect result == 15539, "Test 16 failed";

  result := InsomniaCure(1, 2, 10, 4, 39901);
  expect result == 39901, "Test 17 failed";

  result := InsomniaCure(3, 4, 7, 1, 58048);
  expect result == 58048, "Test 18 failed";

  result := InsomniaCure(9, 10, 4, 6, 52003);
  expect result == 21956, "Test 19 failed";

  result := InsomniaCure(5, 10, 9, 3, 70149);
  expect result == 32736, "Test 20 failed";

  print "All tests passed\n";
}