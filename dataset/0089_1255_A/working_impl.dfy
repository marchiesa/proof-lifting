method ChangingVolume(a: int, b: int) returns (presses: int)
{
  var diff := if a > b then a - b else b - a;
  var fives := diff / 5;
  diff := diff % 5;
  var twos := diff / 2;
  diff := diff % 2;
  var ones := diff;
  presses := fives + twos + ones;
}

method Main()
{
  // Test 1
  var r1 := ChangingVolume(4, 0);
  expect r1 == 2, "Test 1.1 failed";
  var r2 := ChangingVolume(5, 14);
  expect r2 == 3, "Test 1.2 failed";
  var r3 := ChangingVolume(3, 9);
  expect r3 == 2, "Test 1.3 failed";

  // Test 2
  var r4 := ChangingVolume(0, 0);
  expect r4 == 0, "Test 2 failed";

  // Test 3
  var r5 := ChangingVolume(10, 10);
  expect r5 == 0, "Test 3 failed";

  // Test 4
  var r6 := ChangingVolume(0, 5);
  expect r6 == 1, "Test 4 failed";

  // Test 5
  var r7 := ChangingVolume(3, 0);
  expect r7 == 2, "Test 5 failed";

  // Test 6
  var r8 := ChangingVolume(1, 50);
  expect r8 == 11, "Test 6 failed";

  // Test 7
  var r9 := ChangingVolume(50, 1);
  expect r9 == 11, "Test 7 failed";

  // Test 8
  var r10 := ChangingVolume(7, 18);
  expect r10 == 3, "Test 8 failed";

  // Test 9
  var r11 := ChangingVolume(0, 1);
  expect r11 == 1, "Test 9.1 failed";
  var r12 := ChangingVolume(1, 0);
  expect r12 == 1, "Test 9.2 failed";
  var r13 := ChangingVolume(2, 5);
  expect r13 == 2, "Test 9.3 failed";
  var r14 := ChangingVolume(10, 3);
  expect r14 == 2, "Test 9.4 failed";
  var r15 := ChangingVolume(7, 7);
  expect r15 == 0, "Test 9.5 failed";

  // Test 10
  var r16 := ChangingVolume(0, 50);
  expect r16 == 10, "Test 10.1 failed";
  var r17 := ChangingVolume(50, 0);
  expect r17 == 10, "Test 10.2 failed";
  var r18 := ChangingVolume(25, 30);
  expect r18 == 1, "Test 10.3 failed";
  var r19 := ChangingVolume(12, 7);
  expect r19 == 1, "Test 10.4 failed";
  var r20 := ChangingVolume(0, 3);
  expect r20 == 2, "Test 10.5 failed";
  var r21 := ChangingVolume(48, 41);
  expect r21 == 2, "Test 10.6 failed";
  var r22 := ChangingVolume(5, 5);
  expect r22 == 0, "Test 10.7 failed";
  var r23 := ChangingVolume(1, 2);
  expect r23 == 1, "Test 10.8 failed";
  var r24 := ChangingVolume(33, 50);
  expect r24 == 4, "Test 10.9 failed";
  var r25 := ChangingVolume(17, 9);
  expect r25 == 3, "Test 10.10 failed";

  print "All tests passed\n";
}