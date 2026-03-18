method IntegerSequenceDividing(n: int) returns (result: int)
{
  var m := n % 4;
  if m == 0 || m == 3 {
    return 0;
  } else {
    return 1;
  }
}

method Main()
{
  var r1 := IntegerSequenceDividing(3);
  expect r1 == 0, "Test 1 failed: expected 0";

  var r2 := IntegerSequenceDividing(5);
  expect r2 == 1, "Test 2 failed: expected 1";

  var r3 := IntegerSequenceDividing(6);
  expect r3 == 1, "Test 3 failed: expected 1";

  var r4 := IntegerSequenceDividing(2000000000);
  expect r4 == 0, "Test 4 failed: expected 0";

  var r5 := IntegerSequenceDividing(1999999999);
  expect r5 == 0, "Test 5 failed: expected 0";

  var r6 := IntegerSequenceDividing(1999999997);
  expect r6 == 1, "Test 6 failed: expected 1";

  var r7 := IntegerSequenceDividing(1999999998);
  expect r7 == 1, "Test 7 failed: expected 1";

  var r8 := IntegerSequenceDividing(1);
  expect r8 == 1, "Test 8 failed: expected 1";

  var r9 := IntegerSequenceDividing(69420);
  expect r9 == 0, "Test 9 failed: expected 0";

  var r10 := IntegerSequenceDividing(999999998);
  expect r10 == 1, "Test 10 failed: expected 1";

  var r11 := IntegerSequenceDividing(65535);
  expect r11 == 0, "Test 11 failed: expected 0";

  var r12 := IntegerSequenceDividing(27397633);
  expect r12 == 1, "Test 12 failed: expected 1";

  var r13 := IntegerSequenceDividing(46341);
  expect r13 == 1, "Test 13 failed: expected 1";

  var r14 := IntegerSequenceDividing(1000271094);
  expect r14 == 1, "Test 14 failed: expected 1";

  var r15 := IntegerSequenceDividing(84457);
  expect r15 == 1, "Test 15 failed: expected 1";

  var r16 := IntegerSequenceDividing(2);
  expect r16 == 1, "Test 16 failed: expected 1";

  var r17 := IntegerSequenceDividing(250489);
  expect r17 == 1, "Test 17 failed: expected 1";

  var r18 := IntegerSequenceDividing(1777777);
  expect r18 == 1, "Test 18 failed: expected 1";

  var r19 := IntegerSequenceDividing(1825468885);
  expect r19 == 1, "Test 19 failed: expected 1";

  var r20 := IntegerSequenceDividing(4);
  expect r20 == 0, "Test 20 failed: expected 0";

  print "All tests passed\n";
}