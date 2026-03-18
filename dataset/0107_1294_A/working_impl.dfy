method CollectingCoins(a: int, b: int, c: int, n: int) returns (result: bool)
{
  var tot := a + b + c + n;
  if tot % 3 != 0 {
    result := false;
  } else {
    var des := tot / 3;
    if a > des || b > des || c > des {
      result := false;
    } else {
      result := true;
    }
  }
}

method Main()
{
  // Test 1
  var r1 := CollectingCoins(5, 3, 2, 8);
  expect r1 == true, "Test 1.1 failed";
  var r2 := CollectingCoins(100, 101, 102, 105);
  expect r2 == true, "Test 1.2 failed";
  var r3 := CollectingCoins(3, 2, 1, 100000000);
  expect r3 == false, "Test 1.3 failed";
  var r4 := CollectingCoins(10, 20, 15, 14);
  expect r4 == false, "Test 1.4 failed";
  var r5 := CollectingCoins(101, 101, 101, 3);
  expect r5 == true, "Test 1.5 failed";

  // Test 2
  var r6 := CollectingCoins(1, 1, 1, 1111);
  expect r6 == false, "Test 2.1 failed";

  // Test 3
  var r7 := CollectingCoins(3, 798, 437, 1804);
  expect r7 == true, "Test 3.1 failed";

  // Test 4
  var r8 := CollectingCoins(1, 1, 1, 3);
  expect r8 == true, "Test 4.1 failed";
  var r9 := CollectingCoins(5, 3, 2, 8);
  expect r9 == true, "Test 4.2 failed";
  var r10 := CollectingCoins(10, 10, 10, 6);
  expect r10 == true, "Test 4.3 failed";

  // Test 5
  var r11 := CollectingCoins(1, 1, 1, 1);
  expect r11 == false, "Test 5.1 failed";

  // Test 6
  var r12 := CollectingCoins(2, 4, 6, 12);
  expect r12 == true, "Test 6.1 failed";
  var r13 := CollectingCoins(1, 2, 3, 3);
  expect r13 == true, "Test 6.2 failed";
  var r14 := CollectingCoins(5, 5, 5, 3);
  expect r14 == true, "Test 6.3 failed";
  var r15 := CollectingCoins(10, 20, 15, 14);
  expect r15 == false, "Test 6.4 failed";
  var r16 := CollectingCoins(1, 1, 1, 6);
  expect r16 == true, "Test 6.5 failed";

  // Test 7
  var r17 := CollectingCoins(50, 50, 50, 3);
  expect r17 == true, "Test 7.1 failed";

  // Test 8
  var r18 := CollectingCoins(1, 2, 3, 6);
  expect r18 == true, "Test 8.1 failed";
  var r19 := CollectingCoins(4, 4, 4, 1);
  expect r19 == false, "Test 8.2 failed";

  // Test 9
  var r20 := CollectingCoins(1, 1, 1, 1);
  expect r20 == false, "Test 9.1 failed";
  var r21 := CollectingCoins(2, 2, 2, 3);
  expect r21 == true, "Test 9.2 failed";
  var r22 := CollectingCoins(3, 3, 3, 9);
  expect r22 == true, "Test 9.3 failed";
  var r23 := CollectingCoins(1, 2, 3, 4);
  expect r23 == false, "Test 9.4 failed";

  // Test 10
  var r24 := CollectingCoins(7, 3, 1, 10);
  expect r24 == true, "Test 10.1 failed";

  // Test 11
  var r25 := CollectingCoins(10, 10, 10, 1);
  expect r25 == false, "Test 11.1 failed";
  var r26 := CollectingCoins(5, 5, 5, 15);
  expect r26 == true, "Test 11.2 failed";
  var r27 := CollectingCoins(1, 1, 1, 2);
  expect r27 == false, "Test 11.3 failed";

  // Test 12
  var r28 := CollectingCoins(1, 1, 1, 3);
  expect r28 == true, "Test 12.1 failed";
  var r29 := CollectingCoins(2, 3, 4, 1);
  expect r29 == false, "Test 12.2 failed";
  var r30 := CollectingCoins(3, 3, 3, 3);
  expect r30 == true, "Test 12.3 failed";
  var r31 := CollectingCoins(10, 20, 30, 30);
  expect r31 == true, "Test 12.4 failed";
  var r32 := CollectingCoins(1, 2, 3, 5);
  expect r32 == false, "Test 12.5 failed";
  var r33 := CollectingCoins(7, 7, 7, 21);
  expect r33 == true, "Test 12.6 failed";

  // Test 13
  var r34 := CollectingCoins(50, 40, 30, 30);
  expect r34 == true, "Test 13.1 failed";
  var r35 := CollectingCoins(1, 1, 1, 9);
  expect r35 == true, "Test 13.2 failed";

  print "All tests passed\n";
}