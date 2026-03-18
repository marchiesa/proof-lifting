method FindSasuke(a: seq<int>) returns (b: seq<int>)
{
  b := [];
  var i := 0;
  while i < |a|
  {
    if i % 2 == 0 {
      b := b + [a[i + 1]];
    } else {
      b := b + [-a[i - 1]];
    }
    i := i + 1;
  }
}

method Main()
{
  // Test 1
  var r1 := FindSasuke([1, 100]);
  expect r1 == [100, -1], "Test 1.1 failed";

  var r2 := FindSasuke([1, 2, 3, 6]);
  expect r2 == [2, -1, 6, -3], "Test 1.2 failed";

  // Test 2
  var r3 := FindSasuke([-1, 1, 1, 1, 1, 1]);
  expect r3 == [1, 1, 1, -1, 1, -1], "Test 2.1 failed";

  var r4 := FindSasuke([1, -1, 1, 1, 1, 1]);
  expect r4 == [-1, -1, 1, -1, 1, -1], "Test 2.2 failed";

  var r5 := FindSasuke([1, 1, -1, 1, 1, 1]);
  expect r5 == [1, -1, 1, 1, 1, -1], "Test 2.3 failed";

  var r6 := FindSasuke([1, 1, 1, -1, 1, 1]);
  expect r6 == [1, -1, -1, -1, 1, -1], "Test 2.4 failed";

  var r7 := FindSasuke([1, 1, 1, 1, -1, 1]);
  expect r7 == [1, -1, 1, -1, 1, 1], "Test 2.5 failed";

  var r8 := FindSasuke([1, 1, 1, 1, 1, -1]);
  expect r8 == [1, -1, 1, -1, -1, -1], "Test 2.6 failed";

  // Test 3
  var r9 := FindSasuke([1, 1]);
  expect r9 == [1, -1], "Test 3 failed";

  // Test 4
  var r10 := FindSasuke([3, -3]);
  expect r10 == [-3, -3], "Test 4 failed";

  // Test 5
  var r11 := FindSasuke([1, 2, 3, 4]);
  expect r11 == [2, -1, 4, -3], "Test 5 failed";

  // Test 6
  var r12 := FindSasuke([1, 1, 1, 1, 1, 1]);
  expect r12 == [1, -1, 1, -1, 1, -1], "Test 6 failed";

  // Test 7
  var r13 := FindSasuke([5, 10]);
  expect r13 == [10, -5], "Test 7.1 failed";

  var r14 := FindSasuke([-3, 3]);
  expect r14 == [3, 3], "Test 7.2 failed";

  // Test 8
  var r15 := FindSasuke([-1, -2, -3, -4]);
  expect r15 == [-2, 1, -4, 3], "Test 8 failed";

  // Test 9
  var r16 := FindSasuke([1, -1]);
  expect r16 == [-1, -1], "Test 9.1 failed";

  var r17 := FindSasuke([2, 3, -2, -3]);
  expect r17 == [3, -2, -3, 2], "Test 9.2 failed";

  var r18 := FindSasuke([99, 1]);
  expect r18 == [1, -99], "Test 9.3 failed";

  // Test 10
  var r19 := FindSasuke([100, -100]);
  expect r19 == [-100, -100], "Test 10 failed";

  // Test 11
  var r20 := FindSasuke([7, -3, 5, 2]);
  expect r20 == [-3, -7, 2, -5], "Test 11 failed";

  // Test 12
  var r21 := FindSasuke([1, 2]);
  expect r21 == [2, -1], "Test 12.1 failed";

  var r22 := FindSasuke([3, 4]);
  expect r22 == [4, -3], "Test 12.2 failed";

  var r23 := FindSasuke([5, 6]);
  expect r23 == [6, -5], "Test 12.3 failed";

  var r24 := FindSasuke([7, 8]);
  expect r24 == [8, -7], "Test 12.4 failed";

  var r25 := FindSasuke([9, 10]);
  expect r25 == [10, -9], "Test 12.5 failed";

  print "All tests passed\n";
}