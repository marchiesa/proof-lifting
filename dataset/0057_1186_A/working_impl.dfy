method VusContest(n: int, m: int, k: int) returns (result: string)
{
  if k < n || m < n {
    result := "No";
  } else {
    result := "Yes";
  }
}

method Main()
{
  var r1 := VusContest(5, 8, 6);
  expect r1 == "Yes", "Test 1 failed";

  var r2 := VusContest(3, 9, 3);
  expect r2 == "Yes", "Test 2 failed";

  var r3 := VusContest(8, 5, 20);
  expect r3 == "No", "Test 3 failed";

  var r4 := VusContest(1, 1, 1);
  expect r4 == "Yes", "Test 4 failed";

  var r5 := VusContest(54, 82, 100);
  expect r5 == "Yes", "Test 5 failed";

  var r6 := VusContest(1, 100, 100);
  expect r6 == "Yes", "Test 6 failed";

  var r7 := VusContest(100, 99, 99);
  expect r7 == "No", "Test 7 failed";

  var r8 := VusContest(8, 20, 5);
  expect r8 == "No", "Test 8 failed";

  var r9 := VusContest(68, 91, 90);
  expect r9 == "Yes", "Test 9 failed";

  var r10 := VusContest(92, 35, 39);
  expect r10 == "No", "Test 10 failed";

  var r11 := VusContest(20, 84, 93);
  expect r11 == "Yes", "Test 11 failed";

  var r12 := VusContest(44, 28, 47);
  expect r12 == "No", "Test 12 failed";

  var r13 := VusContest(68, 73, 96);
  expect r13 == "Yes", "Test 13 failed";

  var r14 := VusContest(92, 17, 54);
  expect r14 == "No", "Test 14 failed";

  var r15 := VusContest(20, 61, 100);
  expect r15 == "Yes", "Test 15 failed";

  var r16 := VusContest(44, 2, 53);
  expect r16 == "No", "Test 16 failed";

  var r17 := VusContest(68, 54, 3);
  expect r17 == "No", "Test 17 failed";

  var r18 := VusContest(58, 92, 33);
  expect r18 == "No", "Test 18 failed";

  var r19 := VusContest(2, 1, 2);
  expect r19 == "No", "Test 19 failed";

  var r20 := VusContest(2, 2, 1);
  expect r20 == "No", "Test 20 failed";

  print "All tests passed\n";
}