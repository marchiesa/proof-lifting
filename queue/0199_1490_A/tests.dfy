method DenseArray(a: seq<int>) returns (count: int)
{
  count := 0;
  if |a| <= 1 {
    return;
  }
  var l := a[0];
  var i := 1;
  while i < |a|
  {
    var c := a[i];
    while c > l * 2
    {
      l := l * 2;
      count := count + 1;
    }
    while l > c * 2
    {
      l := (l + 1) / 2;
      count := count + 1;
    }
    l := c;
    i := i + 1;
  }
}

method Main()
{
  // Test 1
  var r1 := DenseArray([4, 2, 10, 1]);
  expect r1 == 5, "Test 1a failed";

  var r2 := DenseArray([1, 3]);
  expect r2 == 1, "Test 1b failed";

  var r3 := DenseArray([6, 1]);
  expect r3 == 2, "Test 1c failed";

  var r4 := DenseArray([1, 4, 2]);
  expect r4 == 1, "Test 1d failed";

  var r5 := DenseArray([1, 2, 3, 4, 3]);
  expect r5 == 0, "Test 1e failed";

  var r6 := DenseArray([4, 31, 25, 50, 30, 20, 34, 46, 42, 16, 15, 16]);
  expect r6 == 3, "Test 1f failed";

  // Test 2
  var r7 := DenseArray([1, 2]);
  expect r7 == 0, "Test 2a failed";

  var r8 := DenseArray([3, 6]);
  expect r8 == 0, "Test 2b failed";

  var r9 := DenseArray([7, 50]);
  expect r9 == 2, "Test 2c failed";

  // Test 3
  var r10 := DenseArray([1, 1, 1, 1, 1]);
  expect r10 == 0, "Test 3 failed";

  // Test 4
  var r11 := DenseArray([1, 50]);
  expect r11 == 5, "Test 4 failed";

  // Test 5
  var r12 := DenseArray([50, 1]);
  expect r12 == 5, "Test 5 failed";

  // Test 6
  var r13 := DenseArray([1, 2, 4]);
  expect r13 == 0, "Test 6 failed";

  // Test 7
  var r14 := DenseArray([1, 3, 7, 15, 31, 50, 25, 12, 6, 3]);
  expect r14 == 5, "Test 7 failed";

  // Test 8
  var r15 := DenseArray([25, 25]);
  expect r15 == 0, "Test 8 failed";

  // Test 9
  var r16 := DenseArray([2, 4, 8, 16]);
  expect r16 == 0, "Test 9a failed";

  var r17 := DenseArray([50, 1, 50]);
  expect r17 == 10, "Test 9b failed";

  // Test 10
  var r18 := DenseArray([1, 2, 1, 2, 1, 2]);
  expect r18 == 0, "Test 10 failed";

  // Test 11
  var r19 := DenseArray([1, 1]);
  expect r19 == 0, "Test 11a failed";

  var r20 := DenseArray([1, 2]);
  expect r20 == 0, "Test 11b failed";

  var r21 := DenseArray([2, 1]);
  expect r21 == 0, "Test 11c failed";

  var r22 := DenseArray([3, 5, 11]);
  expect r22 == 1, "Test 11d failed";

  var r23 := DenseArray([48, 24, 12, 6]);
  expect r23 == 0, "Test 11e failed";

  print "All tests passed\n";
}