method DefiniteGame(v: int) returns (result: int)
{
  if v == 2 {
    return 2;
  } else {
    return 1;
  }
}

method Main()
{
  var r1 := DefiniteGame(8);
  expect r1 == 1, "Test 1 failed";

  var r2 := DefiniteGame(1);
  expect r2 == 1, "Test 2 failed";

  var r3 := DefiniteGame(4);
  expect r3 == 1, "Test 3 failed";

  var r4 := DefiniteGame(3);
  expect r4 == 1, "Test 4 failed";

  var r5 := DefiniteGame(158260522);
  expect r5 == 1, "Test 5 failed";

  var r6 := DefiniteGame(2);
  expect r6 == 2, "Test 6 failed";

  var r7 := DefiniteGame(1000000000);
  expect r7 == 1, "Test 7 failed";

  var r8 := DefiniteGame(5);
  expect r8 == 1, "Test 8 failed";

  var r9 := DefiniteGame(7);
  expect r9 == 1, "Test 9 failed";

  var r10 := DefiniteGame(9);
  expect r10 == 1, "Test 10 failed";

  var r11 := DefiniteGame(10);
  expect r11 == 1, "Test 11 failed";

  var r12 := DefiniteGame(11);
  expect r12 == 1, "Test 12 failed";

  var r13 := DefiniteGame(12);
  expect r13 == 1, "Test 13 failed";

  var r14 := DefiniteGame(13);
  expect r14 == 1, "Test 14 failed";

  var r15 := DefiniteGame(641009859);
  expect r15 == 1, "Test 15 failed";

  var r16 := DefiniteGame(802593587);
  expect r16 == 1, "Test 16 failed";

  var r17 := DefiniteGame(819819);
  expect r17 == 1, "Test 17 failed";

  var r18 := DefiniteGame(524125987);
  expect r18 == 1, "Test 18 failed";

  var r19 := DefiniteGame(959461493);
  expect r19 == 1, "Test 19 failed";

  var r20 := DefiniteGame(33313246);
  expect r20 == 1, "Test 20 failed";

  print "All tests passed\n";
}