method SpyDetected(a: seq<int>) returns (idx: int)
{
  var i := 0;
  while i < |a|
  {
    var count := 0;
    var j := 0;
    while j < |a|
    {
      if a[j] == a[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    if count == 1 {
      return i + 1;
    }
    i := i + 1;
  }
  return 0;
}

method Main()
{
  // Test 1
  var r1 := SpyDetected([11, 13, 11, 11]);
  expect r1 == 2, "Test 1a failed";
  var r2 := SpyDetected([1, 4, 4, 4, 4]);
  expect r2 == 1, "Test 1b failed";
  var r3 := SpyDetected([3, 3, 3, 3, 10, 3, 3, 3, 3, 3]);
  expect r3 == 5, "Test 1c failed";
  var r4 := SpyDetected([20, 20, 10]);
  expect r4 == 3, "Test 1d failed";

  // Test 2
  var r5 := SpyDetected([5, 6, 6]);
  expect r5 == 1, "Test 2a failed";
  var r6 := SpyDetected([7, 7, 6]);
  expect r6 == 3, "Test 2b failed";

  // Test 3
  var r7 := SpyDetected([5, 5, 1]);
  expect r7 == 3, "Test 3a failed";
  var r8 := SpyDetected([2, 2, 2, 7]);
  expect r8 == 4, "Test 3b failed";
  var r9 := SpyDetected([9, 3, 9]);
  expect r9 == 2, "Test 3c failed";

  // Test 4
  var r10 := SpyDetected([6, 6, 6, 6, 3]);
  expect r10 == 5, "Test 4 failed";

  // Test 5
  var r11 := SpyDetected([1, 2, 1]);
  expect r11 == 2, "Test 5a failed";
  var r12 := SpyDetected([4, 4, 4, 4, 4, 9]);
  expect r12 == 6, "Test 5b failed";

  // Test 6
  var r13 := SpyDetected([8, 8, 8, 1, 8, 8, 8]);
  expect r13 == 4, "Test 6 failed";

  // Test 7
  var r14 := SpyDetected([50, 10, 50]);
  expect r14 == 2, "Test 7 failed";

  // Test 8
  var r15 := SpyDetected([3, 3, 7, 3]);
  expect r15 == 3, "Test 8a failed";
  var r16 := SpyDetected([2, 2, 2, 5, 2]);
  expect r16 == 4, "Test 8b failed";

  // Test 9
  var r17 := SpyDetected([1, 1, 1, 1, 1, 1, 1, 1, 1, 7]);
  expect r17 == 10, "Test 9 failed";

  // Test 10
  var r18 := SpyDetected([4, 9, 4]);
  expect r18 == 2, "Test 10 failed";

  // Test 11
  var r19 := SpyDetected([11, 11, 11, 11, 2]);
  expect r19 == 5, "Test 11a failed";
  var r20 := SpyDetected([6, 1, 6]);
  expect r20 == 2, "Test 11b failed";
  var r21 := SpyDetected([3, 3, 3, 8]);
  expect r21 == 4, "Test 11c failed";

  // Test 12
  var r22 := SpyDetected([5, 5, 5, 5, 5, 2]);
  expect r22 == 6, "Test 12 failed";

  print "All tests passed\n";
}