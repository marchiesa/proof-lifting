method BinaryDecimal(n: int) returns (result: int)
{
  result := 0;
  var num := n;
  while num > 0 {
    var digit := num % 10;
    if digit > result {
      result := digit;
    }
    num := num / 10;
  }
}

method Main()
{
  // Test 1
  var r1 := BinaryDecimal(121);
  expect r1 == 2, "Test 1a failed";
  var r2 := BinaryDecimal(5);
  expect r2 == 5, "Test 1b failed";
  var r3 := BinaryDecimal(1000000000);
  expect r3 == 1, "Test 1c failed";

  // Test 2
  var r4 := BinaryDecimal(1);
  expect r4 == 1, "Test 2 failed";

  // Test 3
  var r5 := BinaryDecimal(10);
  expect r5 == 1, "Test 3 failed";

  // Test 4
  var r6 := BinaryDecimal(9);
  expect r6 == 9, "Test 4 failed";

  // Test 5
  var r7 := BinaryDecimal(11);
  expect r7 == 1, "Test 5 failed";

  // Test 6
  var r8 := BinaryDecimal(25);
  expect r8 == 5, "Test 6 failed";

  // Test 7
  var r9 := BinaryDecimal(50);
  expect r9 == 5, "Test 7 failed";

  // Test 8
  var r10 := BinaryDecimal(1);
  expect r10 == 1, "Test 8a failed";
  var r11 := BinaryDecimal(2);
  expect r11 == 2, "Test 8b failed";
  var r12 := BinaryDecimal(3);
  expect r12 == 3, "Test 8c failed";

  // Test 9
  var r13 := BinaryDecimal(9);
  expect r13 == 9, "Test 9a failed";
  var r14 := BinaryDecimal(19);
  expect r14 == 9, "Test 9b failed";
  var r15 := BinaryDecimal(21);
  expect r15 == 2, "Test 9c failed";
  var r16 := BinaryDecimal(30);
  expect r16 == 3, "Test 9d failed";
  var r17 := BinaryDecimal(45);
  expect r17 == 5, "Test 9e failed";

  // Test 10
  var r18 := BinaryDecimal(49);
  expect r18 == 9, "Test 10a failed";
  var r19 := BinaryDecimal(50);
  expect r19 == 5, "Test 10b failed";

  // Test 11
  var r20 := BinaryDecimal(11);
  expect r20 == 1, "Test 11a failed";
  var r21 := BinaryDecimal(33);
  expect r21 == 3, "Test 11b failed";
  var r22 := BinaryDecimal(7);
  expect r22 == 7, "Test 11c failed";
  var r23 := BinaryDecimal(18);
  expect r23 == 8, "Test 11d failed";

  print "All tests passed\n";
}