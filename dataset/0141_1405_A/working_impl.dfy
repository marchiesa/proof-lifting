method PermutationForgery(p: seq<int>) returns (p': seq<int>)
{
  p' := [];
  var i := |p|;
  while i > 0
  {
    i := i - 1;
    p' := p' + [p[i]];
  }
}

method Main()
{
  // Test 1 / Test 2: [1,2] -> [2,1]
  var r1 := PermutationForgery([1, 2]);
  expect r1 == [2, 1], "Test 1 failed";

  // Test 1 / Test 6: [2,1,6,5,4,3] -> [3,4,5,6,1,2]
  var r2 := PermutationForgery([2, 1, 6, 5, 4, 3]);
  expect r2 == [3, 4, 5, 6, 1, 2], "Test 2 failed";

  // Test 1 / Test 5: [2,4,3,1,5] -> [5,1,3,4,2]
  var r3 := PermutationForgery([2, 4, 3, 1, 5]);
  expect r3 == [5, 1, 3, 4, 2], "Test 3 failed";

  // Test 3: [1,3,2] -> [2,3,1]
  var r4 := PermutationForgery([1, 3, 2]);
  expect r4 == [2, 3, 1], "Test 4 failed";

  // Test 4: [1,4,2,3] -> [3,2,4,1]
  var r5 := PermutationForgery([1, 4, 2, 3]);
  expect r5 == [3, 2, 4, 1], "Test 5 failed";

  // Test 7: [3,1,2] -> [2,1,3]
  var r6 := PermutationForgery([3, 1, 2]);
  expect r6 == [2, 1, 3], "Test 6 failed";

  // Test 7: [4,1,3,2] -> [2,3,1,4]
  var r7 := PermutationForgery([4, 1, 3, 2]);
  expect r7 == [2, 3, 1, 4], "Test 7 failed";

  // Test 8: [1,2,3,4,5,6,7] -> [7,6,5,4,3,2,1]
  var r8 := PermutationForgery([1, 2, 3, 4, 5, 6, 7]);
  expect r8 == [7, 6, 5, 4, 3, 2, 1], "Test 8 failed";

  // Test 9: [8,6,4,2,1,3,5,7] -> [7,5,3,1,2,4,6,8]
  var r9 := PermutationForgery([8, 6, 4, 2, 1, 3, 5, 7]);
  expect r9 == [7, 5, 3, 1, 2, 4, 6, 8], "Test 9 failed";

  // Test 10: [2,1] -> [1,2]
  var r10 := PermutationForgery([2, 1]);
  expect r10 == [1, 2], "Test 10 failed";

  // Test 10: [2,3,1] -> [1,3,2]
  var r11 := PermutationForgery([2, 3, 1]);
  expect r11 == [1, 3, 2], "Test 11 failed";

  // Test 10: [3,1,4,2] -> [2,4,1,3]
  var r12 := PermutationForgery([3, 1, 4, 2]);
  expect r12 == [2, 4, 1, 3], "Test 12 failed";

  // Test 11: [5,3,1,2,4] -> [4,2,1,3,5]
  var r13 := PermutationForgery([5, 3, 1, 2, 4]);
  expect r13 == [4, 2, 1, 3, 5], "Test 13 failed";

  // Test 11: [6,1,5,2,4,3] -> [3,4,2,5,1,6]
  var r14 := PermutationForgery([6, 1, 5, 2, 4, 3]);
  expect r14 == [3, 4, 2, 5, 1, 6], "Test 14 failed";

  print "All tests passed\n";
}