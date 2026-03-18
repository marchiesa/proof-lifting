method ThreePilesOfCandies(a: int, b: int, c: int) returns (maxCandies: int)
{
  maxCandies := (a + b + c) / 2;
}

method Main()
{
  // Test 1, case 1
  var r1 := ThreePilesOfCandies(1, 3, 4);
  expect r1 == 4, "Test 1.1 failed";

  // Test 1, case 2
  var r2 := ThreePilesOfCandies(1, 10, 100);
  expect r2 == 55, "Test 1.2 failed";

  // Test 1, case 3
  var r3 := ThreePilesOfCandies(10000000000000000, 10000000000000000, 10000000000000000);
  expect r3 == 15000000000000000, "Test 1.3 failed";

  // Test 1, case 4
  var r4 := ThreePilesOfCandies(23, 34, 45);
  expect r4 == 51, "Test 1.4 failed";

  // Test 2, case 1
  var r5 := ThreePilesOfCandies(111, 2, 3);
  expect r5 == 58, "Test 2.1 failed";

  print "All tests passed\n";
}