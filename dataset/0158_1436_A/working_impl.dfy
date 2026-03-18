method Reorder(a: seq<int>, m: int) returns (result: bool)
{
  var s := 0;
  for i := 0 to |a| {
    s := s + a[i];
  }
  result := m == s;
}

method Main()
{
  var r: bool;

  // Test 1, case 1: a=[2,5,1], m=8 → YES
  r := Reorder([2, 5, 1], 8);
  expect r == true, "Test 1.1 failed: expected true";

  // Test 1, case 2: a=[0,1,2,3], m=4 → NO
  r := Reorder([0, 1, 2, 3], 4);
  expect r == false, "Test 1.2 failed: expected false";

  // Test 2: a=[2,4], m=2 → NO
  r := Reorder([2, 4], 2);
  expect r == false, "Test 2 failed: expected false";

  // Test 3: a=[3,6], m=3 → NO
  r := Reorder([3, 6], 3);
  expect r == false, "Test 3 failed: expected false";

  // Test 4: a=[0,0,0], m=0 → YES
  r := Reorder([0, 0, 0], 0);
  expect r == true, "Test 4 failed: expected true";

  // Test 5: a=[2,2,2], m=2 → NO
  r := Reorder([2, 2, 2], 2);
  expect r == false, "Test 5 failed: expected false";

  // Test 6: a=[1,1,1], m=1 → NO
  r := Reorder([1, 1, 1], 1);
  expect r == false, "Test 6 failed: expected false";

  // Test 7, case 1: a=[5,5,5,5], m=5 → NO
  r := Reorder([5, 5, 5, 5], 5);
  expect r == false, "Test 7.1 failed: expected false";

  // Test 7, case 2: a=[3,3,3,3,3,3], m=3 → NO
  r := Reorder([3, 3, 3, 3, 3, 3], 3);
  expect r == false, "Test 7.2 failed: expected false";

  // Test 8: a=[0,0,0], m=3 → NO
  r := Reorder([0, 0, 0], 3);
  expect r == false, "Test 8 failed: expected false";

  // Test 9: a=[2], m=1 → NO
  r := Reorder([2], 1);
  expect r == false, "Test 9 failed: expected false";

  // Test 10: a=[2,2,2], m=3 → NO
  r := Reorder([2, 2, 2], 3);
  expect r == false, "Test 10 failed: expected false";

  // Test 11: a=[10,13,9], m=8 → NO
  r := Reorder([10, 13, 9], 8);
  expect r == false, "Test 11 failed: expected false";

  // Test 12: a=[1], m=0 → NO
  r := Reorder([1], 0);
  expect r == false, "Test 12 failed: expected false";

  // Test 13: a=[16,0,0], m=8 → NO
  r := Reorder([16, 0, 0], 8);
  expect r == false, "Test 13 failed: expected false";

  // Test 14: a=[88,9,9,9,9,9], m=1 → NO
  r := Reorder([88, 9, 9, 9, 9, 9], 1);
  expect r == false, "Test 14 failed: expected false";

  // Test 15: a=[0], m=1 → NO
  r := Reorder([0], 1);
  expect r == false, "Test 15 failed: expected false";

  // Test 16: a=[4], m=2 → NO
  r := Reorder([4], 2);
  expect r == false, "Test 16 failed: expected false";

  // Test 17: a=[2,4,10], m=8 → NO
  r := Reorder([2, 4, 10], 8);
  expect r == false, "Test 17 failed: expected false";

  // Test 18: a=[5,10,15], m=5 → NO
  r := Reorder([5, 10, 15], 5);
  expect r == false, "Test 18 failed: expected false";

  // Test 19: a=[0,0,0], m=2 → NO
  r := Reorder([0, 0, 0], 2);
  expect r == false, "Test 19 failed: expected false";

  // Test 20: a=[15,8,1], m=8 → NO
  r := Reorder([15, 8, 1], 8);
  expect r == false, "Test 20 failed: expected false";

  print "All tests passed\n";
}