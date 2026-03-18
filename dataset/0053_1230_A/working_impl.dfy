method DawidAndCandies(a1: int, a2: int, a3: int, a4: int) returns (result: bool)
{
  result := (a1 + a2 == a3 + a4) || (a1 + a3 == a2 + a4) || (a1 + a4 == a2 + a3) ||
            (a1 + a2 + a3 == a4) || (a1 + a2 + a4 == a3) || (a1 + a3 + a4 == a2) || (a2 + a3 + a4 == a1);
}

method Main()
{
  var r1 := DawidAndCandies(1, 7, 11, 5);
  expect r1 == true, "Test 1 failed";

  var r2 := DawidAndCandies(7, 3, 2, 5);
  expect r2 == false, "Test 2 failed";

  var r3 := DawidAndCandies(3, 14, 36, 53);
  expect r3 == true, "Test 3 failed";

  var r4 := DawidAndCandies(30, 74, 41, 63);
  expect r4 == true, "Test 4 failed";

  var r5 := DawidAndCandies(92, 69, 83, 97);
  expect r5 == false, "Test 5 failed";

  var r6 := DawidAndCandies(26, 52, 7, 19);
  expect r6 == true, "Test 6 failed";

  var r7 := DawidAndCandies(72, 52, 62, 62);
  expect r7 == true, "Test 7 failed";

  var r8 := DawidAndCandies(1, 1, 1, 1);
  expect r8 == true, "Test 8 failed";

  var r9 := DawidAndCandies(70, 100, 10, 86);
  expect r9 == false, "Test 9 failed";

  var r10 := DawidAndCandies(14, 10, 18, 24);
  expect r10 == false, "Test 10 failed";

  var r11 := DawidAndCandies(20, 14, 37, 71);
  expect r11 == true, "Test 11 failed";

  var r12 := DawidAndCandies(1, 1, 2, 1);
  expect r12 == false, "Test 12 failed";

  var r13 := DawidAndCandies(2, 4, 1, 1);
  expect r13 == true, "Test 13 failed";

  var r14 := DawidAndCandies(34, 11, 84, 39);
  expect r14 == true, "Test 14 failed";

  var r15 := DawidAndCandies(76, 97, 99, 74);
  expect r15 == true, "Test 15 failed";

  var r16 := DawidAndCandies(44, 58, 90, 53);
  expect r16 == false, "Test 16 failed";

  var r17 := DawidAndCandies(18, 88, 18, 18);
  expect r17 == false, "Test 17 failed";

  var r18 := DawidAndCandies(48, 14, 3, 31);
  expect r18 == true, "Test 18 failed";

  var r19 := DawidAndCandies(72, 96, 2, 26);
  expect r19 == true, "Test 19 failed";

  var r20 := DawidAndCandies(69, 7, 44, 30);
  expect r20 == false, "Test 20 failed";

  print "All tests passed\n";
}