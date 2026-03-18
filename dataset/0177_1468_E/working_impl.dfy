method FourSegments(a: seq<int>) returns (area: int)
{
  // Find max value and its index
  var maxVal := a[0];
  var maxIdx := 0;
  var i := 1;
  while i < |a|
  {
    if a[i] > maxVal {
      maxVal := a[i];
      maxIdx := i;
    }
    i := i + 1;
  }

  // Build remaining sequence without the first max
  var remaining: seq<int> := [];
  i := 0;
  while i < |a|
  {
    if i != maxIdx {
      remaining := remaining + [a[i]];
    }
    i := i + 1;
  }

  // Find min and max of remaining
  var lo := remaining[0];
  var hi := remaining[0];
  i := 1;
  while i < |remaining|
  {
    if remaining[i] < lo {
      lo := remaining[i];
    }
    if remaining[i] > hi {
      hi := remaining[i];
    }
    i := i + 1;
  }

  area := lo * hi;
  return;
}

method Main()
{
  // Test 1
  var r1 := FourSegments([1, 2, 3, 4]);
  expect r1 == 3, "Test 1.1 failed";

  var r2 := FourSegments([5, 5, 5, 5]);
  expect r2 == 25, "Test 1.2 failed";

  var r3 := FourSegments([3, 1, 4, 1]);
  expect r3 == 3, "Test 1.3 failed";

  var r4 := FourSegments([100, 20, 20, 100]);
  expect r4 == 2000, "Test 1.4 failed";

  // Test 2
  var r5 := FourSegments([1, 1, 1, 1]);
  expect r5 == 1, "Test 2 failed";

  // Test 3
  var r6 := FourSegments([2, 3, 2, 3]);
  expect r6 == 6, "Test 3 failed";

  // Test 5
  var r7 := FourSegments([1, 2, 1, 2]);
  expect r7 == 2, "Test 5 failed";

  // Test 6
  var r8 := FourSegments([2, 3, 4, 5]);
  expect r8 == 8, "Test 6.2 failed";

  var r9 := FourSegments([10, 10, 10, 10]);
  expect r9 == 100, "Test 6.3 failed";

  // Test 7
  var r10 := FourSegments([1, 50, 1, 50]);
  expect r10 == 50, "Test 7.1 failed";

  var r11 := FourSegments([7, 3, 7, 3]);
  expect r11 == 21, "Test 7.2 failed";

  // Test 8
  var r12 := FourSegments([1, 1, 50, 50]);
  expect r12 == 50, "Test 8 failed";

  // Test 9
  var r13 := FourSegments([3, 4, 3, 4]);
  expect r13 == 12, "Test 9.1 failed";

  var r14 := FourSegments([5, 1, 5, 1]);
  expect r14 == 5, "Test 9.3 failed";

  var r15 := FourSegments([10, 20, 10, 20]);
  expect r15 == 200, "Test 9.4 failed";

  var r16 := FourSegments([2, 2, 2, 2]);
  expect r16 == 4, "Test 9.5 failed";

  // Test 10
  var r17 := FourSegments([50, 50, 50, 50]);
  expect r17 == 2500, "Test 10 failed";

  // Test 11
  var r18 := FourSegments([1, 1, 1, 50]);
  expect r18 == 1, "Test 11.1 failed";

  var r19 := FourSegments([25, 25, 25, 25]);
  expect r19 == 625, "Test 11.2 failed";

  print "All tests passed\n";
}