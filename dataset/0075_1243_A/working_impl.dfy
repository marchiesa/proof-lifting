method MaximumSquare(a: seq<int>) returns (side: int)
{
  var n := |a|;
  var arr := new int[n];
  var k := 0;
  while k < n {
    arr[k] := a[k];
    k := k + 1;
  }

  // Sort descending (insertion sort)
  var i := 1;
  while i < n {
    var key := arr[i];
    var j := i - 1;
    while j >= 0 && arr[j] < key {
      arr[j + 1] := arr[j];
      j := j - 1;
    }
    arr[j + 1] := key;
    i := i + 1;
  }

  // Find largest side s where at least s elements >= s
  side := n;
  i := 0;
  while i < n {
    if arr[i] < i + 1 {
      side := i;
      return;
    }
    i := i + 1;
  }

  return;
}

method Main()
{
  // Test 1, case 1
  var r1 := MaximumSquare([4, 3, 1, 4, 5]);
  expect r1 == 3, "Test 1.1 failed";

  // Test 1, case 2
  var r2 := MaximumSquare([4, 4, 4, 4]);
  expect r2 == 4, "Test 1.2 failed";

  // Test 1, case 3
  var r3 := MaximumSquare([1, 1, 1]);
  expect r3 == 1, "Test 1.3 failed";

  // Test 1, case 4
  var r4 := MaximumSquare([5, 5, 1, 1, 5]);
  expect r4 == 3, "Test 1.4 failed";

  // Test 2, case 1
  var r5 := MaximumSquare([1]);
  expect r5 == 1, "Test 2.1 failed";

  // Test 2, case 2
  var r6 := MaximumSquare([2, 1]);
  expect r6 == 1, "Test 2.2 failed";

  // Test 2, case 3
  var r7 := MaximumSquare([3, 1, 2]);
  expect r7 == 2, "Test 2.3 failed";

  // Test 2, case 4
  var r8 := MaximumSquare([2, 2, 2]);
  expect r8 == 2, "Test 2.4 failed";

  // Test 2, case 5
  var r9 := MaximumSquare([4, 1, 4, 1]);
  expect r9 == 2, "Test 2.5 failed";

  // Test 2, case 6
  var r10 := MaximumSquare([5, 4, 3, 2, 1]);
  expect r10 == 3, "Test 2.6 failed";

  // Test 2, case 7
  var r11 := MaximumSquare([1, 2, 3, 4, 5]);
  expect r11 == 3, "Test 2.7 failed";

  // Test 2, case 8
  var r12 := MaximumSquare([3, 2, 1, 6, 2, 2]);
  expect r12 == 2, "Test 2.8 failed";

  // Test 2, case 9
  var r13 := MaximumSquare([4, 5, 2, 9, 6, 10, 3, 7, 1, 8]);
  expect r13 == 5, "Test 2.9 failed";

  // Test 2, case 10
  var r14 := MaximumSquare([1, 3, 2, 2, 2, 9, 10, 10, 9, 7]);
  expect r14 == 5, "Test 2.10 failed";

  print "All tests passed\n";
}