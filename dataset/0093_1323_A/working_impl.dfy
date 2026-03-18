method EvenSubsetSum(a: seq<int>) returns (indices: seq<int>)
{
  var n := |a|;
  if n == 1 && a[0] % 2 == 1 {
    indices := [-1];
  } else {
    var ind := -1;
    var ind2 := -1;
    var ind3 := -1;
    var j := 0;
    while j < n
    {
      if a[j] % 2 == 0 {
        ind := j;
      } else if ind2 == -1 {
        ind2 := j;
      } else {
        ind3 := j;
      }
      j := j + 1;
    }
    if ind == -1 {
      indices := [ind2 + 1, ind3 + 1];
    } else {
      indices := [ind + 1];
    }
  }
}

method Main()
{
  // Test 1, case 1: a=[1,4,3] → [2]
  var r1 := EvenSubsetSum([1, 4, 3]);
  expect r1 == [2], "Test 1.1 failed";

  // Test 1, case 2: a=[15] → [-1]
  var r2 := EvenSubsetSum([15]);
  expect r2 == [-1], "Test 1.2 failed";

  // Test 1, case 3: a=[3,5] → [1,2]
  var r3 := EvenSubsetSum([3, 5]);
  expect r3 == [1, 2], "Test 1.3 failed";

  // Test 2, case 1: a=[1,1] → [1,2]
  var r4 := EvenSubsetSum([1, 1]);
  expect r4 == [1, 2], "Test 2.1 failed";

  // Test 3, case 1: a=[2] → [1]
  var r5 := EvenSubsetSum([2]);
  expect r5 == [1], "Test 3.1 failed";

  // Test 3, case 2: a=[1] → [-1]
  var r6 := EvenSubsetSum([1]);
  expect r6 == [-1], "Test 3.2 failed";

  // Test 3, case 3: a=[2,2] → [2]
  var r7 := EvenSubsetSum([2, 2]);
  expect r7 == [2], "Test 3.3 failed";

  // Test 3, case 4: a=[2,1] → [1]
  var r8 := EvenSubsetSum([2, 1]);
  expect r8 == [1], "Test 3.4 failed";

  // Test 3, case 5: a=[1,2] → [2]
  var r9 := EvenSubsetSum([1, 2]);
  expect r9 == [2], "Test 3.5 failed";

  // Test 3, case 6: a=[1,1] → [1,2]
  var r10 := EvenSubsetSum([1, 1]);
  expect r10 == [1, 2], "Test 3.6 failed";

  // Test 3, case 7: a=[2,2,2] → [3]
  var r11 := EvenSubsetSum([2, 2, 2]);
  expect r11 == [3], "Test 3.7 failed";

  // Test 3, case 8: a=[2,2,1] → [2]
  var r12 := EvenSubsetSum([2, 2, 1]);
  expect r12 == [2], "Test 3.8 failed";

  // Test 3, case 9: a=[2,1,2] → [3]
  var r13 := EvenSubsetSum([2, 1, 2]);
  expect r13 == [3], "Test 3.9 failed";

  // Test 3, case 10: a=[2,1,1] → [1]
  var r14 := EvenSubsetSum([2, 1, 1]);
  expect r14 == [1], "Test 3.10 failed";

  // Test 3, case 11: a=[1,2,2] → [3]
  var r15 := EvenSubsetSum([1, 2, 2]);
  expect r15 == [3], "Test 3.11 failed";

  // Test 3, case 12: a=[1,2,1] → [2]
  var r16 := EvenSubsetSum([1, 2, 1]);
  expect r16 == [2], "Test 3.12 failed";

  // Test 3, case 13: a=[1,1,2] → [3]
  var r17 := EvenSubsetSum([1, 1, 2]);
  expect r17 == [3], "Test 3.13 failed";

  // Test 3, case 14: a=[1,1,1] → [1,3]
  var r18 := EvenSubsetSum([1, 1, 1]);
  expect r18 == [1, 3], "Test 3.14 failed";

  print "All tests passed\n";
}