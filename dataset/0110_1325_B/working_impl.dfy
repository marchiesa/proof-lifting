method CopyCopyCopyCopyCopy(a: seq<int>) returns (result: int)
{
  var n := |a|;
  if n == 0 {
    return 0;
  }
  var arr := new int[n];
  var i := 0;
  while i < n
  {
    arr[i] := a[i];
    i := i + 1;
  }
  // Insertion sort
  var j := 1;
  while j < n
  {
    var key := arr[j];
    var k := j - 1;
    while k >= 0 && arr[k] > key
    {
      arr[k + 1] := arr[k];
      k := k - 1;
    }
    arr[k + 1] := key;
    j := j + 1;
  }
  // Count distinct by subtracting consecutive duplicates
  var ans := n;
  var m := 0;
  while m < n - 1
  {
    if arr[m + 1] == arr[m] {
      ans := ans - 1;
    }
    m := m + 1;
  }
  return ans;
}

method Main()
{
  // Test 1
  var r1 := CopyCopyCopyCopyCopy([3, 2, 1]);
  expect r1 == 3, "Test 1a failed";
  var r2 := CopyCopyCopyCopyCopy([3, 1, 4, 1, 5, 9]);
  expect r2 == 5, "Test 1b failed";

  // Test 2
  var r3 := CopyCopyCopyCopyCopy([6, 6, 8, 8, 6, 6, 6]);
  expect r3 == 2, "Test 2a failed";
  var r4 := CopyCopyCopyCopyCopy([2]);
  expect r4 == 1, "Test 2b failed";
  var r5 := CopyCopyCopyCopyCopy([4, 5, 9, 8, 7]);
  expect r5 == 5, "Test 2c failed";
  var r6 := CopyCopyCopyCopyCopy([1, 2, 7, 1, 6, 10, 2]);
  expect r6 == 5, "Test 2d failed";

  // Test 3
  var r7 := CopyCopyCopyCopyCopy([5, 5, 5, 5, 5]);
  expect r7 == 1, "Test 3a failed";
  var r8 := CopyCopyCopyCopyCopy([1, 2, 5]);
  expect r8 == 3, "Test 3b failed";

  // Test 4
  var r9 := CopyCopyCopyCopyCopy([1, 2, 3, 4, 5]);
  expect r9 == 5, "Test 4a failed";
  var r10 := CopyCopyCopyCopyCopy([2, 3, 4, 5]);
  expect r10 == 4, "Test 4b failed";

  // Test 5
  var r11 := CopyCopyCopyCopyCopy([1, 1, 274005660]);
  expect r11 == 2, "Test 5 failed";

  // Test 6
  var r12 := CopyCopyCopyCopyCopy([1, 1]);
  expect r12 == 1, "Test 6a failed";
  var r13 := CopyCopyCopyCopyCopy([1]);
  expect r13 == 1, "Test 6b failed";

  // Test 7
  var r14 := CopyCopyCopyCopyCopy([1, 3, 3, 3]);
  expect r14 == 2, "Test 7a failed";
  var r15 := CopyCopyCopyCopyCopy([1, 2, 3]);
  expect r15 == 3, "Test 7b failed";

  // Test 8
  var r16 := CopyCopyCopyCopyCopy([1, 1, 1]);
  expect r16 == 1, "Test 8a failed";
  var r17 := CopyCopyCopyCopyCopy([1, 1]);
  expect r17 == 1, "Test 8b failed";

  // Test 9
  var r18 := CopyCopyCopyCopyCopy([1, 3, 4, 5, 2]);
  expect r18 == 5, "Test 9 failed";

  print "All tests passed\n";
}