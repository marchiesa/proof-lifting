method SumDigits(x: int) returns (s: int)
  decreases *
{
  s := 0;
  var tmp := x;
  while tmp > 0
    decreases *
  {
    s := s + tmp % 10;
    tmp := tmp / 10;
  }
}

method NearestInterestingNumber(a: int) returns (n: int)
  decreases *
{
  n := a;
  var s := SumDigits(n);
  while s != 18
    decreases *
  {
    n := n + 1;
    s := SumDigits(n);
  }
}

method Main()
  decreases *
{
  var r1 := NearestInterestingNumber(432);
  expect r1 == 459, "Test 1 failed";

  var r2 := NearestInterestingNumber(99);
  expect r2 == 99, "Test 2 failed";

  var r3 := NearestInterestingNumber(237);
  expect r3 == 279, "Test 3 failed";

  var r4 := NearestInterestingNumber(42);
  expect r4 == 99, "Test 4 failed";

  var r5 := NearestInterestingNumber(1);
  expect r5 == 99, "Test 5 failed";

  var r6 := NearestInterestingNumber(2);
  expect r6 == 99, "Test 6 failed";

  var r7 := NearestInterestingNumber(1000);
  expect r7 == 1089, "Test 7 failed";

  var r8 := NearestInterestingNumber(898);
  expect r8 == 909, "Test 8 failed";

  var r9 := NearestInterestingNumber(997);
  expect r9 == 1089, "Test 9 failed";

  var r10 := NearestInterestingNumber(999);
  expect r10 == 1089, "Test 10 failed";

  var r11 := NearestInterestingNumber(399);
  expect r11 == 459, "Test 11 failed";

  var r12 := NearestInterestingNumber(8);
  expect r12 == 99, "Test 12 failed";

  var r13 := NearestInterestingNumber(120);
  expect r13 == 189, "Test 13 failed";

  var r14 := NearestInterestingNumber(909);
  expect r14 == 909, "Test 14 failed";

  var r15 := NearestInterestingNumber(9);
  expect r15 == 99, "Test 15 failed";

  var r16 := NearestInterestingNumber(398);
  expect r16 == 459, "Test 16 failed";

  var r17 := NearestInterestingNumber(7);
  expect r17 == 99, "Test 17 failed";

  var r18 := NearestInterestingNumber(799);
  expect r18 == 819, "Test 18 failed";

  var r19 := NearestInterestingNumber(970);
  expect r19 == 972, "Test 19 failed";

  var r20 := NearestInterestingNumber(188);
  expect r20 == 189, "Test 20 failed";

  print "All tests passed\n";
}