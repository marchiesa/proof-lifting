method NonZero(a: seq<int>) returns (steps: int)
{
  var s := 0;
  var z := 0;
  var i := 0;
  while i < |a|
  {
    s := s + a[i];
    if a[i] == 0 {
      z := z + 1;
    }
    i := i + 1;
  }
  if s + z == 0 {
    return z + 1;
  } else {
    return z;
  }
}

method Main()
{
  // Test 1, case 1
  var r1 := NonZero([2, -1, -1]);
  expect r1 == 1, "Test 1.1 failed";

  // Test 1, case 2
  var r2 := NonZero([-1, 0, 0, 1]);
  expect r2 == 2, "Test 1.2 failed";

  // Test 1, case 3
  var r3 := NonZero([-1, 2]);
  expect r3 == 0, "Test 1.3 failed";

  // Test 1, case 4
  var r4 := NonZero([0, -2, 1]);
  expect r4 == 2, "Test 1.4 failed";

  // Test 2
  var r5 := NonZero([0]);
  expect r5 == 1, "Test 2 failed";

  // Test 3: 100 elements all 64
  var r6 := NonZero(seq(100, i => 64));
  expect r6 == 0, "Test 3 failed";

  // Test 4: 100 elements alternating 64, -64
  var r7 := NonZero(seq(100, i => if i % 2 == 0 then 64 else -64));
  expect r7 == 1, "Test 4 failed";

  // Test 5: 84 specific elements
  var r8 := NonZero([-95, -42, 85, 39, 3, 30, -80, 26, -28, 46, -55, -27, 13, 99, 3, 98, 18, 17, 57, -35, 8, -97, -8, 13, -5, 65, 6, 38, 42, -96, 55, -67, 98, -39, 94, 25, 18, -22, -57, -99, 22, 49, -34, -38, -8, -84, -10, 16, -35, 16, 91, 9, 98, -20, 31, 34, 86, -2, 23, 99, 31, 28, -1, -19, 42, 49, 14, 36, -33, 6, 97, 18, -27, 22, -22, 46, -58, -88, -36, -98, -59, 37, 3, 2]);
  expect r8 == 0, "Test 5 failed";

  // Test 6: 64 elements alternating 2, -2
  var r9 := NonZero(seq(64, i => if i % 2 == 0 then 2 else -2));
  expect r9 == 1, "Test 6 failed";

  // Test 7: 49 twos followed by -98
  var r10 := NonZero(seq(49, i => 2) + [-98]);
  expect r10 == 1, "Test 7 failed";

  print "All tests passed\n";
}