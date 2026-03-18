method PerfectlyImperfectArray(a: seq<int>) returns (result: bool)
{
  result := false;
  var i := 0;
  while i < |a|
  {
    var x := a[i];
    var s := 0;
    while s * s < x
    {
      s := s + 1;
    }
    if s * s != x {
      result := true;
      return;
    }
    i := i + 1;
  }
}

method Main()
{
  // Test 1
  var r1 := PerfectlyImperfectArray([1, 5, 4]);
  expect r1 == true, "Test 1a failed";
  var r2 := PerfectlyImperfectArray([100, 10000]);
  expect r2 == false, "Test 1b failed";

  // Test 2
  var r3 := PerfectlyImperfectArray([1]);
  expect r3 == false, "Test 2a failed";
  var r4 := PerfectlyImperfectArray([2]);
  expect r4 == true, "Test 2b failed";
  var r5 := PerfectlyImperfectArray([3]);
  expect r5 == true, "Test 2c failed";

  // Test 3
  var r6 := PerfectlyImperfectArray([3, 3, 3, 3, 3]);
  expect r6 == true, "Test 3 failed";

  // Test 4
  var r7 := PerfectlyImperfectArray([3, 12]);
  expect r7 == true, "Test 4a failed";
  var r8 := PerfectlyImperfectArray([3, 3]);
  expect r8 == true, "Test 4b failed";
  var r9 := PerfectlyImperfectArray([12, 4, 3]);
  expect r9 == true, "Test 4c failed";

  // Test 5
  var r10 := PerfectlyImperfectArray([7, 7, 28]);
  expect r10 == true, "Test 5 failed";

  // Test 6
  var r11 := PerfectlyImperfectArray([2, 2]);
  expect r11 == true, "Test 6 failed";

  // Test 7
  var r12 := PerfectlyImperfectArray([1412, 1412]);
  expect r12 == true, "Test 7 failed";

  // Test 8
  var r13 := PerfectlyImperfectArray([3]);
  expect r13 == true, "Test 8 failed";

  // Test 9
  var r14 := PerfectlyImperfectArray([5]);
  expect r14 == true, "Test 9 failed";

  // Test 10
  var r15 := PerfectlyImperfectArray([6]);
  expect r15 == true, "Test 10 failed";

  // Test 11
  var r16 := PerfectlyImperfectArray([1412]);
  expect r16 == true, "Test 11 failed";

  // Test 12
  var r17 := PerfectlyImperfectArray([3, 12]);
  expect r17 == true, "Test 12a failed";
  var r18 := PerfectlyImperfectArray([8, 2]);
  expect r18 == true, "Test 12b failed";
  var r19 := PerfectlyImperfectArray([12, 4, 3]);
  expect r19 == true, "Test 12c failed";

  // Test 13
  var r20 := PerfectlyImperfectArray([3, 3]);
  expect r20 == true, "Test 13a failed";
  var r21 := PerfectlyImperfectArray([1, 1, 1, 1, 1]);
  expect r21 == false, "Test 13b failed";
  var r22 := PerfectlyImperfectArray([1, 1, 1, 1, 1, 1]);
  expect r22 == false, "Test 13c failed";
  var r23 := PerfectlyImperfectArray([2, 2, 4, 4, 4]);
  expect r23 == true, "Test 13d failed";
  var r24 := PerfectlyImperfectArray([4, 4, 4, 4, 4]);
  expect r24 == false, "Test 13e failed";

  // Test 14
  var r25 := PerfectlyImperfectArray([7]);
  expect r25 == true, "Test 14 failed";

  // Test 15
  var r26 := PerfectlyImperfectArray([1]);
  expect r26 == false, "Test 15a failed";
  var r27 := PerfectlyImperfectArray([2]);
  expect r27 == true, "Test 15b failed";

  // Test 16
  var r28 := PerfectlyImperfectArray([6, 6]);
  expect r28 == true, "Test 16 failed";

  // Test 17
  var r29 := PerfectlyImperfectArray([3, 2, 1, 1, 1]);
  expect r29 == true, "Test 17 failed";

  // Test 18
  var r30 := PerfectlyImperfectArray([2, 8]);
  expect r30 == true, "Test 18 failed";

  // Test 19
  var r31 := PerfectlyImperfectArray([3, 3]);
  expect r31 == true, "Test 19 failed";

  // Test 20
  var r32 := PerfectlyImperfectArray([2]);
  expect r32 == true, "Test 20 failed";

  print "All tests passed\n";
}