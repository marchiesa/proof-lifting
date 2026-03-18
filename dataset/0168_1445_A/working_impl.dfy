method ArrayRearrangement(a: seq<int>, b: seq<int>, x: int) returns (result: bool)
{
  var n := |a|;
  var i := 0;
  while i < n
  {
    if a[i] + b[n - 1 - i] > x {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // Test 1.1 / Test 5: a=[1,2,3], b=[1,1,2], x=4 → true
  var r1 := ArrayRearrangement([1, 2, 3], [1, 1, 2], 4);
  expect r1 == true, "Test 1.1 failed";

  // Test 1.2 / Test 7.1: a=[1,4], b=[2,5], x=6 → true
  var r2 := ArrayRearrangement([1, 4], [2, 5], 6);
  expect r2 == true, "Test 1.2 failed";

  // Test 1.3: a=[1,2,3,4], b=[1,2,3,4], x=4 → false
  var r3 := ArrayRearrangement([1, 2, 3, 4], [1, 2, 3, 4], 4);
  expect r3 == false, "Test 1.3 failed";

  // Test 1.4 / Test 4 / Test 7.2: a=[5], b=[5], x=5 → false
  var r4 := ArrayRearrangement([5], [5], 5);
  expect r4 == false, "Test 1.4 failed";

  // Test 2: a=[1], b=[1], x=1 → false
  var r5 := ArrayRearrangement([1], [1], 1);
  expect r5 == false, "Test 2 failed";

  // Test 3: a=[1], b=[1], x=5 → true
  var r6 := ArrayRearrangement([1], [1], 5);
  expect r6 == true, "Test 3 failed";

  // Test 6: a=[1,2,3,4,5], b=[1,2,3,4,5], x=10 → true
  var r7 := ArrayRearrangement([1, 2, 3, 4, 5], [1, 2, 3, 4, 5], 10);
  expect r7 == true, "Test 6 failed";

  // Test 8: a=[1,3,5,7], b=[1,2,4,6], x=8 → true
  var r8 := ArrayRearrangement([1, 3, 5, 7], [1, 2, 4, 6], 8);
  expect r8 == true, "Test 8 failed";

  // Test 9: a=[1], b=[1], x=2 → true
  var r9 := ArrayRearrangement([1], [1], 2);
  expect r9 == true, "Test 9 failed";

  // Test 10: a=[1,1,2,3,4,5], b=[1,2,3,4,5,6], x=7 → true
  var r10 := ArrayRearrangement([1, 1, 2, 3, 4, 5], [1, 2, 3, 4, 5, 6], 7);
  expect r10 == true, "Test 10 failed";

  // Test 11.1: a=[1,5], b=[2,3], x=10 → true
  var r11 := ArrayRearrangement([1, 5], [2, 3], 10);
  expect r11 == true, "Test 11.1 failed";

  // Test 11.2: a=[1,2,3], b=[1,2,3], x=6 → true
  var r12 := ArrayRearrangement([1, 2, 3], [1, 2, 3], 6);
  expect r12 == true, "Test 11.2 failed";

  // Test 11.3: a=[10,20,30,40], b=[5,10,15,20], x=50 → true
  var r13 := ArrayRearrangement([10, 20, 30, 40], [5, 10, 15, 20], 50);
  expect r13 == true, "Test 11.3 failed";

  // Test 12: a=[1,2,3,4,5], b=[1,2,3,4,5], x=5 → false
  var r14 := ArrayRearrangement([1, 2, 3, 4, 5], [1, 2, 3, 4, 5], 5);
  expect r14 == false, "Test 12 failed";

  // Test 13: a=[1..10], b=[2,4,6,8,10,11,12,13,14,15], x=20 → true
  var r15 := ArrayRearrangement([1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [2, 4, 6, 8, 10, 11, 12, 13, 14, 15], 20);
  expect r15 == true, "Test 13 failed";

  print "All tests passed\n";
}