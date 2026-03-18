method RemoveAProgression(n: int, x: int) returns (result: int)
{
  return x * 2;
}

method Main()
{
  // Test 1
  var r1 := RemoveAProgression(3, 1);
  expect r1 == 2, "Test 1a failed";
  var r2 := RemoveAProgression(4, 2);
  expect r2 == 4, "Test 1b failed";
  var r3 := RemoveAProgression(69, 6);
  expect r3 == 12, "Test 1c failed";

  // Test 2
  var r4 := RemoveAProgression(1000000000, 1);
  expect r4 == 2, "Test 2a failed";
  var r5 := RemoveAProgression(1000000000, 500000000);
  expect r5 == 1000000000, "Test 2b failed";

  // Test 3
  var r6 := RemoveAProgression(2441139, 10);
  expect r6 == 20, "Test 3 failed";

  // Test 4
  var r7 := RemoveAProgression(2441139, 1);
  expect r7 == 2, "Test 4 failed";

  // Test 5
  var r8 := RemoveAProgression(244139, 1);
  expect r8 == 2, "Test 5 failed";

  // Test 6
  var r9 := RemoveAProgression(2441139, 12);
  expect r9 == 24, "Test 6 failed";

  // Test 7
  var r10 := RemoveAProgression(241139, 1);
  expect r10 == 2, "Test 7 failed";

  // Test 8
  var r11 := RemoveAProgression(244119, 1);
  expect r11 == 2, "Test 8 failed";

  // Test 9
  var r12 := RemoveAProgression(2441139, 2);
  expect r12 == 4, "Test 9 failed";

  // Test 10
  var r13 := RemoveAProgression(2451199, 2);
  expect r13 == 4, "Test 10 failed";

  // Test 11
  var r14 := RemoveAProgression(2452199, 2);
  expect r14 == 4, "Test 11 failed";

  print "All tests passed\n";
}