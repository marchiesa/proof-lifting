method ParkLighting(n: int, m: int) returns (lanterns: int)
{
  var x := n * m;
  x := x + 1;
  lanterns := x / 2;
}

method Main()
{
  // Test 1
  var r1 := ParkLighting(1, 1);
  expect r1 == 1, "Test 1a failed";
  var r2 := ParkLighting(1, 3);
  expect r2 == 2, "Test 1b failed";
  var r3 := ParkLighting(2, 2);
  expect r3 == 2, "Test 1c failed";
  var r4 := ParkLighting(3, 3);
  expect r4 == 5, "Test 1d failed";
  var r5 := ParkLighting(5, 3);
  expect r5 == 8, "Test 1e failed";

  // Test 2
  var r6 := ParkLighting(1329, 2007);
  expect r6 == 1333652, "Test 2a failed";
  var r7 := ParkLighting(179, 57);
  expect r7 == 5102, "Test 2b failed";

  // Test 3
  var r8 := ParkLighting(1, 1);
  expect r8 == 1, "Test 3 failed";

  // Test 4
  var r9 := ParkLighting(1, 2);
  expect r9 == 1, "Test 4 failed";

  // Test 5
  var r10 := ParkLighting(2, 3);
  expect r10 == 3, "Test 5 failed";

  // Test 6
  var r11 := ParkLighting(5, 5);
  expect r11 == 13, "Test 6 failed";

  // Test 7
  var r12 := ParkLighting(1, 1);
  expect r12 == 1, "Test 7a failed";
  var r13 := ParkLighting(2, 2);
  expect r13 == 2, "Test 7b failed";
  var r14 := ParkLighting(3, 3);
  expect r14 == 5, "Test 7c failed";

  // Test 8
  var r15 := ParkLighting(1, 3);
  expect r15 == 2, "Test 8a failed";
  var r16 := ParkLighting(2, 2);
  expect r16 == 2, "Test 8b failed";
  var r17 := ParkLighting(3, 3);
  expect r17 == 5, "Test 8c failed";
  var r18 := ParkLighting(5, 3);
  expect r18 == 8, "Test 8d failed";
  var r19 := ParkLighting(4, 4);
  expect r19 == 8, "Test 8e failed";

  // Test 9
  var r20 := ParkLighting(10, 10);
  expect r20 == 50, "Test 9 failed";

  // Test 10
  var r21 := ParkLighting(1, 50);
  expect r21 == 25, "Test 10a failed";
  var r22 := ParkLighting(50, 1);
  expect r22 == 25, "Test 10b failed";
  var r23 := ParkLighting(7, 9);
  expect r23 == 32, "Test 10c failed";
  var r24 := ParkLighting(3, 6);
  expect r24 == 9, "Test 10d failed";

  // Test 11
  var r25 := ParkLighting(1, 1);
  expect r25 == 1, "Test 11a failed";
  var r26 := ParkLighting(50, 50);
  expect r26 == 1250, "Test 11b failed";

  // Test 12
  var r27 := ParkLighting(2, 1);
  expect r27 == 1, "Test 12a failed";
  var r28 := ParkLighting(1, 4);
  expect r28 == 2, "Test 12b failed";
  var r29 := ParkLighting(3, 5);
  expect r29 == 8, "Test 12c failed";
  var r30 := ParkLighting(4, 2);
  expect r30 == 4, "Test 12d failed";
  var r31 := ParkLighting(6, 7);
  expect r31 == 21, "Test 12e failed";
  var r32 := ParkLighting(8, 3);
  expect r32 == 12, "Test 12f failed";

  print "All tests passed\n";
}