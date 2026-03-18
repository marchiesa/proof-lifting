method Heist(a: seq<int>) returns (stolen: int)
{
  if |a| == 0 {
    return 0;
  }
  var lo := a[0];
  var hi := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < lo {
      lo := a[i];
    }
    if a[i] > hi {
      hi := a[i];
    }
    i := i + 1;
  }
  var res := hi - lo + 1 - |a|;
  if res < 0 {
    return 0;
  }
  return res;
}

method Main()
{
  // Test 1
  var r1 := Heist([10, 13, 12, 8]);
  expect r1 == 2, "Test 1 failed";

  // Test 2
  var r2 := Heist([7, 5, 6, 4, 8]);
  expect r2 == 0, "Test 2 failed";

  // Test 3
  var r3 := Heist([2]);
  expect r3 == 0, "Test 3 failed";

  // Test 4
  var r4 := Heist([1000000000, 500000000, 2]);
  expect r4 == 999999996, "Test 4 failed";

  // Test 5
  var r5 := Heist([793, 656, 534, 608, 971, 970, 670, 786, 978, 665, 92, 391, 328, 228, 340, 681, 495, 175, 659, 520, 179, 396, 554, 481, 631, 468, 799, 390, 563, 471]);
  expect r5 == 857, "Test 5 failed";

  // Test 6
  var r6 := Heist([194, 121, 110, 134, 172, 142, 195, 135, 186, 187, 128, 161, 185, 132, 117, 175, 178, 131, 143, 151, 170, 181, 188, 140, 133, 145, 119, 129, 179, 149, 109, 123, 124, 106, 100, 199, 197, 155, 141, 183]);
  expect r6 == 60, "Test 6 failed";

  // Test 7
  var r7 := Heist([96, 4, 9, 94, 31, 70, 45, 24, 67, 64, 77, 100, 89, 75, 38, 60, 8, 49, 28, 32]);
  expect r7 == 77, "Test 7 failed";

  // Test 8
  var r8 := Heist([10, 1]);
  expect r8 == 8, "Test 8 failed";

  // Test 9
  var r9 := Heist([796461544, 559476582]);
  expect r9 == 236984961, "Test 9 failed";

  // Test 10
  var r10 := Heist([65, 81, 6]);
  expect r10 == 73, "Test 10 failed";

  // Test 11
  var r11 := Heist([2830, 6117, 3663, 4414, 7223, 6665, 1779, 5891, 7065, 6591]);
  expect r11 == 5435, "Test 11 failed";

  // Test 12
  var r12 := Heist([1, 1000000000]);
  expect r12 == 999999998, "Test 12 failed";

  // Test 13
  var r13 := Heist([1000000000]);
  expect r13 == 0, "Test 13 failed";

  // Test 14
  var r14 := Heist([100000000]);
  expect r14 == 0, "Test 14 failed";

  // Test 15
  var r15 := Heist([10000000, 10000001, 10000002]);
  expect r15 == 0, "Test 15 failed";

  // Test 16
  var r16 := Heist([999999999, 1000000000]);
  expect r16 == 0, "Test 16 failed";

  // Test 17
  var r17 := Heist([999999998, 1000000000]);
  expect r17 == 1, "Test 17 failed";

  // Test 18
  var r18 := Heist([100000000, 100000001, 100000002]);
  expect r18 == 0, "Test 18 failed";

  // Test 19
  var r19 := Heist([1, 2, 4, 5, 6]);
  expect r19 == 1, "Test 19 failed";

  // Test 20
  var r20 := Heist([10000000, 100000000]);
  expect r20 == 89999999, "Test 20 failed";

  print "All tests passed\n";
}