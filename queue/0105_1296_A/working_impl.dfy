method ArrayWithOddSum(a: seq<int>) returns (result: bool)
{
  var sm := 0;
  for i := 0 to |a| {
    sm := sm + a[i];
  }
  if sm % 2 != 0 {
    result := true;
  } else {
    var od := 0;
    var ev := 0;
    for i := 0 to |a| {
      if a[i] % 2 != 0 {
        od := od + 1;
      } else {
        ev := ev + 1;
      }
    }
    if od == 0 || ev == 0 {
      result := false;
    } else {
      result := true;
    }
  }
}

method Main()
{
  // Test 1: 5 sub-cases
  var r1 := ArrayWithOddSum([2, 3]);
  expect r1 == true, "Test 1a: [2,3] expected YES";

  var r2 := ArrayWithOddSum([2, 2, 8, 8]);
  expect r2 == false, "Test 1b: [2,2,8,8] expected NO";

  var r3 := ArrayWithOddSum([3, 3, 3]);
  expect r3 == true, "Test 1c: [3,3,3] expected YES";

  var r4 := ArrayWithOddSum([5, 5, 5, 5]);
  expect r4 == false, "Test 1d: [5,5,5,5] expected NO";

  var r5 := ArrayWithOddSum([1, 1, 1, 1]);
  expect r5 == false, "Test 1e: [1,1,1,1] expected NO";

  // Test 2
  var r6 := ArrayWithOddSum([114]);
  expect r6 == false, "Test 2: [114] expected NO";

  // Test 3: 3 sub-cases
  var r7 := ArrayWithOddSum([7]);
  expect r7 == true, "Test 3a: [7] expected YES";

  var r8 := ArrayWithOddSum([1, 2]);
  expect r8 == true, "Test 3b: [1,2] expected YES";

  var r9 := ArrayWithOddSum([3, 3, 3]);
  expect r9 == true, "Test 3c: [3,3,3] expected YES";

  // Test 4
  var r10 := ArrayWithOddSum([2, 4, 6, 8, 10]);
  expect r10 == false, "Test 4: [2,4,6,8,10] expected NO";

  // Test 5
  var r11 := ArrayWithOddSum([1]);
  expect r11 == true, "Test 5: [1] expected YES";

  // Test 6: 2 sub-cases
  var r12 := ArrayWithOddSum([1, 1, 1]);
  expect r12 == true, "Test 6a: [1,1,1] expected YES";

  var r13 := ArrayWithOddSum([2, 2, 2]);
  expect r13 == false, "Test 6b: [2,2,2] expected NO";

  // Test 7
  var r14 := ArrayWithOddSum([3, 5, 7, 9]);
  expect r14 == false, "Test 7: [3,5,7,9] expected NO";

  // Test 8
  var r15 := ArrayWithOddSum([2, 2, 2, 2, 2, 2]);
  expect r15 == false, "Test 8: [2,2,2,2,2,2] expected NO";

  // Test 9
  var r16 := ArrayWithOddSum([1, 2]);
  expect r16 == true, "Test 9: [1,2] expected YES";

  // Test 10: 4 sub-cases
  var r17 := ArrayWithOddSum([50]);
  expect r17 == false, "Test 10a: [50] expected NO";

  var r18 := ArrayWithOddSum([3]);
  expect r18 == true, "Test 10b: [3] expected YES";

  var r19 := ArrayWithOddSum([7, 7]);
  expect r19 == false, "Test 10c: [7,7] expected NO";

  var r20 := ArrayWithOddSum([2, 4, 6]);
  expect r20 == false, "Test 10d: [2,4,6] expected NO";

  // Test 11
  var r21 := ArrayWithOddSum([1, 3, 5, 7, 9]);
  expect r21 == true, "Test 11: [1,3,5,7,9] expected YES";

  // Test 12: 2 sub-cases
  var r22 := ArrayWithOddSum([2, 2, 2, 3]);
  expect r22 == true, "Test 12a: [2,2,2,3] expected YES";

  var r23 := ArrayWithOddSum([4, 4, 4]);
  expect r23 == false, "Test 12b: [4,4,4] expected NO";

  print "All tests passed\n";
}