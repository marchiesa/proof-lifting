method PetyaAndOrigami(n: int, k: int) returns (notebooks: int)
{
  notebooks := ((n * 2 + k - 1) / k) + ((n * 5 + k - 1) / k) + ((n * 8 + k - 1) / k);
}

method Main()
{
  var result: int;

  result := PetyaAndOrigami(3, 5);
  expect result == 10, "Test 1 failed";

  result := PetyaAndOrigami(15, 6);
  expect result == 38, "Test 2 failed";

  result := PetyaAndOrigami(1, 1);
  expect result == 15, "Test 3 failed";

  result := PetyaAndOrigami(100000000, 1);
  expect result == 1500000000, "Test 4 failed";

  result := PetyaAndOrigami(1, 100000000);
  expect result == 3, "Test 5 failed";

  result := PetyaAndOrigami(96865066, 63740710);
  expect result == 25, "Test 6 failed";

  result := PetyaAndOrigami(58064619, 65614207);
  expect result == 15, "Test 7 failed";

  result := PetyaAndOrigami(31115339, 39163052);
  expect result == 13, "Test 8 failed";

  result := PetyaAndOrigami(14231467, 12711896);
  expect result == 18, "Test 9 failed";

  result := PetyaAndOrigami(92314891, 81228036);
  expect result == 19, "Test 10 failed";

  result := PetyaAndOrigami(75431019, 54776881);
  expect result == 22, "Test 11 failed";

  result := PetyaAndOrigami(48481739, 28325725);
  expect result == 27, "Test 12 failed";

  result := PetyaAndOrigami(99784030, 7525);
  expect result == 198906, "Test 13 failed";

  result := PetyaAndOrigami(72834750, 9473);
  expect result == 115332, "Test 14 failed";

  result := PetyaAndOrigami(55950878, 8318);
  expect result == 100898, "Test 15 failed";

  result := PetyaAndOrigami(34034303, 7162);
  expect result == 71283, "Test 16 failed";

  result := PetyaAndOrigami(17150431, 3302);
  expect result == 77910, "Test 17 failed";

  result := PetyaAndOrigami(90201151, 4851);
  expect result == 278916, "Test 18 failed";

  result := PetyaAndOrigami(73317279, 991);
  expect result == 1109749, "Test 19 failed";

  result := PetyaAndOrigami(51400703, 5644);
  expect result == 136609, "Test 20 failed";

  print "All tests passed\n";
}