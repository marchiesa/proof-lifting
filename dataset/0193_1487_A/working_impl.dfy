method Arena(n: int, a: seq<int>) returns (count: int)
{
  var min_hero := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < min_hero {
      min_hero := a[i];
    }
    i := i + 1;
  }
  count := 0;
  i := 0;
  while i < |a|
  {
    if a[i] > min_hero {
      count := count + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  // Test 1
  var r1 := Arena(3, [3, 2, 2]);
  expect r1 == 1, "Test 1a failed";

  var r2 := Arena(2, [5, 5]);
  expect r2 == 0, "Test 1b failed";

  var r3 := Arena(4, [1, 3, 3, 7]);
  expect r3 == 3, "Test 1c failed";

  // Test 2
  var r4 := Arena(5, [1, 1, 1, 1, 1]);
  expect r4 == 0, "Test 2a failed";

  var r5 := Arena(4, [1, 1, 1, 1]);
  expect r5 == 0, "Test 2b failed";

  // Test 3
  var r6 := Arena(6, [6, 6, 6, 6, 6, 6]);
  expect r6 == 0, "Test 3a failed";

  var r7 := Arena(5, [6, 6, 6, 6, 6]);
  expect r7 == 0, "Test 3b failed";

  // Test 4
  var r8 := Arena(3, [2, 2, 2]);
  expect r8 == 0, "Test 4a failed";

  var r9 := Arena(2, [2, 2]);
  expect r9 == 0, "Test 4b failed";

  // Test 5
  var r10 := Arena(5, [1, 1, 1, 1, 2]);
  expect r10 == 1, "Test 5a failed";

  var r11 := Arena(4, [2, 2, 2, 2]);
  expect r11 == 0, "Test 5b failed";

  // Test 6
  var r12 := Arena(3, [90, 91, 92]);
  expect r12 == 2, "Test 6 failed";

  // Test 7
  var r13 := Arena(3, [1, 1, 1]);
  expect r13 == 0, "Test 7a failed";

  var r14 := Arena(2, [1, 1]);
  expect r14 == 0, "Test 7b failed";

  // Test 8
  var r15 := Arena(4, [1, 1, 1, 1]);
  expect r15 == 0, "Test 8a failed";

  var r16 := Arena(3, [1, 1, 1]);
  expect r16 == 0, "Test 8b failed";

  // Test 9
  var r17 := Arena(3, [3, 3, 3]);
  expect r17 == 0, "Test 9a failed";

  var r18 := Arena(2, [3, 3]);
  expect r18 == 0, "Test 9b failed";

  // Test 10
  var r19 := Arena(4, [5, 5, 5, 5]);
  expect r19 == 0, "Test 10a failed";

  var r20 := Arena(2, [5, 5]);
  expect r20 == 0, "Test 10b failed";

  // Test 11
  var r21 := Arena(4, [5, 5, 5, 5]);
  expect r21 == 0, "Test 11a failed";

  var r22 := Arena(3, [5, 5, 5]);
  expect r22 == 0, "Test 11b failed";

  // Test 12
  var r23 := Arena(4, [1, 2, 4, 4]);
  expect r23 == 3, "Test 12a failed";

  var r24 := Arena(2, [4, 4]);
  expect r24 == 0, "Test 12b failed";

  // Test 13
  var r25 := Arena(4, [1, 1, 1, 1]);
  expect r25 == 0, "Test 13a failed";

  var r26 := Arena(2, [1, 1]);
  expect r26 == 0, "Test 13b failed";

  // Test 14
  var r27 := Arena(4, [2, 2, 2, 3]);
  expect r27 == 1, "Test 14a failed";

  var r28 := Arena(2, [2, 2]);
  expect r28 == 0, "Test 14b failed";

  // Test 15
  var r29 := Arena(8, [1, 9, 1, 9, 8, 10, 10, 10]);
  expect r29 == 6, "Test 15a failed";

  var r30 := Arena(5, [10, 10, 10, 10, 10]);
  expect r30 == 0, "Test 15b failed";

  // Test 16
  var r31 := Arena(5, [1, 1, 1, 1, 1]);
  expect r31 == 0, "Test 16a failed";

  var r32 := Arena(3, [1, 1, 1]);
  expect r32 == 0, "Test 16b failed";

  // Test 17
  var r33 := Arena(3, [4, 4, 4]);
  expect r33 == 0, "Test 17a failed";

  var r34 := Arena(2, [4, 4]);
  expect r34 == 0, "Test 17b failed";

  // Test 18
  var r35 := Arena(5, [9, 3, 3, 4, 100]);
  expect r35 == 3, "Test 18a failed";

  var r36 := Arena(4, [100, 100, 100, 100]);
  expect r36 == 0, "Test 18b failed";

  // Test 19
  var r37 := Arena(5, [1, 2, 3, 5, 5]);
  expect r37 == 4, "Test 19a failed";

  var r38 := Arena(3, [5, 5, 5]);
  expect r38 == 0, "Test 19b failed";

  // Test 20
  var r39 := Arena(4, [1, 1, 2, 2]);
  expect r39 == 2, "Test 20a failed";

  var r40 := Arena(2, [2, 2]);
  expect r40 == 0, "Test 20b failed";

  print "All tests passed\n";
}