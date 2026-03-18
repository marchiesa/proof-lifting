method GradeAllocation(a: seq<int>, m: int) returns (score: int)
{
  var s := 0;
  var i := 0;
  while i < |a|
  {
    s := s + a[i];
    i := i + 1;
  }
  if s < m {
    score := s;
  } else {
    score := m;
  }
}

method Main()
{
  // Test 1, case 1: a=[1,2,3,4], m=10 → 10
  var r1 := GradeAllocation([1, 2, 3, 4], 10);
  expect r1 == 10, "Test 1.1 failed";

  // Test 1, case 2: a=[1,2,3,4], m=5 → 5
  var r2 := GradeAllocation([1, 2, 3, 4], 5);
  expect r2 == 5, "Test 1.2 failed";

  // Test 2, cases 1-12: single student with score 0, varying m
  var r3 := GradeAllocation([0], 1);
  expect r3 == 0, "Test 2.1 failed";

  var r4 := GradeAllocation([0], 2);
  expect r4 == 0, "Test 2.2 failed";

  var r5 := GradeAllocation([0], 5);
  expect r5 == 0, "Test 2.3 failed";

  var r6 := GradeAllocation([0], 10);
  expect r6 == 0, "Test 2.4 failed";

  var r7 := GradeAllocation([0], 50);
  expect r7 == 0, "Test 2.5 failed";

  var r8 := GradeAllocation([0], 100);
  expect r8 == 0, "Test 2.6 failed";

  var r9 := GradeAllocation([0], 500);
  expect r9 == 0, "Test 2.7 failed";

  var r10 := GradeAllocation([0], 1000);
  expect r10 == 0, "Test 2.8 failed";

  var r11 := GradeAllocation([0], 5000);
  expect r11 == 0, "Test 2.9 failed";

  var r12 := GradeAllocation([0], 10000);
  expect r12 == 0, "Test 2.10 failed";

  var r13 := GradeAllocation([0], 50000);
  expect r13 == 0, "Test 2.11 failed";

  var r14 := GradeAllocation([0], 100000);
  expect r14 == 0, "Test 2.12 failed";

  // Test 2, cases 13-18: single student with nonzero score
  var r15 := GradeAllocation([4], 5);
  expect r15 == 4, "Test 2.13 failed";

  var r16 := GradeAllocation([5], 5);
  expect r16 == 5, "Test 2.14 failed";

  var r17 := GradeAllocation([9], 10);
  expect r17 == 9, "Test 2.15 failed";

  var r18 := GradeAllocation([10], 10);
  expect r18 == 10, "Test 2.16 failed";

  var r19 := GradeAllocation([9999], 100000);
  expect r19 == 9999, "Test 2.17 failed";

  var r20 := GradeAllocation([100000], 100000);
  expect r20 == 100000, "Test 2.18 failed";

  var r21 := GradeAllocation([386], 4999);
  expect r21 == 386, "Test 2.19 failed";

  var r22 := GradeAllocation([1], 100000);
  expect r22 == 1, "Test 2.20 failed";

  // Test 2, cases 21-27: four students
  var r23 := GradeAllocation([1, 0, 0, 0], 5);
  expect r23 == 1, "Test 2.21 failed";

  var r24 := GradeAllocation([0, 1, 0, 0], 5);
  expect r24 == 1, "Test 2.22 failed";

  var r25 := GradeAllocation([0, 0, 0, 0], 5);
  expect r25 == 0, "Test 2.23 failed";

  var r26 := GradeAllocation([5, 5, 5, 5], 5);
  expect r26 == 5, "Test 2.24 failed";

  var r27 := GradeAllocation([4, 4, 5, 5], 5);
  expect r27 == 5, "Test 2.25 failed";

  var r28 := GradeAllocation([5, 4, 4, 4], 5);
  expect r28 == 5, "Test 2.26 failed";

  var r29 := GradeAllocation([4, 0, 0, 0], 5);
  expect r29 == 4, "Test 2.27 failed";

  print "All tests passed\n";
}