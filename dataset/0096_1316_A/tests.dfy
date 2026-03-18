function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

predicate ValidScores(a: seq<int>, m: int)
{
  forall i | 0 <= i < |a| :: 0 <= a[i] <= m
}

predicate Achievable(a: seq<int>, m: int, v: int)
  requires |a| > 0
{
  0 <= v <= m &&
  Sum(a) - v >= 0 &&
  Sum(a) - v <= (|a| - 1) * m
}

method GradeAllocation(a: seq<int>, m: int) returns (score: int)
  requires |a| > 0
  requires m >= 0
  requires ValidScores(a, m)
  ensures Achievable(a, m, score)
  ensures forall v | score < v <= m :: !Achievable(a, m, v)
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

predicate IsMaxAchievable(a: seq<int>, m: int, score: int)
  requires |a| > 0
{
  Achievable(a, m, score) &&
  forall v | score < v <= m :: !Achievable(a, m, v)
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Small inputs (seq length 1-3, values 0-5, m <= 5)

  // From test 2.1: [0], m=1 -> 0
  expect IsMaxAchievable([0], 1, 0), "spec positive 1";
  // From test 2.2: [0], m=2 -> 0
  expect IsMaxAchievable([0], 2, 0), "spec positive 2";
  // From test 2.3: [0], m=5 -> 0
  expect IsMaxAchievable([0], 5, 0), "spec positive 3";
  // From test 2.13: [4], m=5 -> 4
  expect IsMaxAchievable([4], 5, 4), "spec positive 4";
  // From test 2.14: [5], m=5 -> 5
  expect IsMaxAchievable([5], 5, 5), "spec positive 5";
  // Scaled from test 1.1 ([1,2,3,4] m=10): [1,2], m=5 -> 3
  expect IsMaxAchievable([1, 2], 5, 3), "spec positive 6";
  // Scaled from test 1.2 ([1,2,3,4] m=5): [2,3], m=5 -> 5
  expect IsMaxAchievable([2, 3], 5, 5), "spec positive 7";
  // Scaled from test 2.21 ([1,0,0,0] m=5): [1,0,0], m=5 -> 1
  expect IsMaxAchievable([1, 0, 0], 5, 1), "spec positive 8";
  // Scaled from test 2.23 ([0,0,0,0] m=5): [0,0,0], m=5 -> 0
  expect IsMaxAchievable([0, 0, 0], 5, 0), "spec positive 9";
  // Scaled from test 2.24 ([5,5,5,5] m=5): [5,5], m=5 -> 5
  expect IsMaxAchievable([5, 5], 5, 5), "spec positive 10";

  // ===== SPEC NEGATIVE TESTS =====
  // Wrong outputs that the spec must reject

  // From neg 2: [0] m=1, wrong=1 (correct=0; sum=0, can't achieve 1)
  expect !IsMaxAchievable([0], 1, 1), "spec negative 1";
  // Scaled: [0] m=2, wrong=1
  expect !IsMaxAchievable([0], 2, 1), "spec negative 2";
  // Scaled: [0] m=5, wrong=1
  expect !IsMaxAchievable([0], 5, 1), "spec negative 3";
  // From neg 1 (score>m): [1,2] m=5, wrong=6
  expect !IsMaxAchievable([1, 2], 5, 6), "spec negative 4";
  // [4] m=5, wrong=5 (sum=4, can't achieve 5)
  expect !IsMaxAchievable([4], 5, 5), "spec negative 5";
  // [5] m=5, wrong=4 (single student, remainder 1 > 0 slots)
  expect !IsMaxAchievable([5], 5, 4), "spec negative 6";
  // [1,2] m=5, wrong=2 (not maximal: 3 is achievable)
  expect !IsMaxAchievable([1, 2], 5, 2), "spec negative 7";
  // [1,0,0] m=5, wrong=0 (not maximal: 1 is achievable)
  expect !IsMaxAchievable([1, 0, 0], 5, 0), "spec negative 8";
  // [0,0,0] m=5, wrong=1 (sum=0, can't achieve 1)
  expect !IsMaxAchievable([0, 0, 0], 5, 1), "spec negative 9";
  // [5,5] m=5, wrong=4 (remainder 6 > 1*5, can't distribute)
  expect !IsMaxAchievable([5, 5], 5, 4), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  // Full-size test pairs

  // Test 1
  var r1 := GradeAllocation([1, 2, 3, 4], 10);
  expect r1 == 10, "impl test 1 failed";
  var r2 := GradeAllocation([1, 2, 3, 4], 5);
  expect r2 == 5, "impl test 2 failed";

  // Test 2: single student, score 0
  var r3 := GradeAllocation([0], 1);
  expect r3 == 0, "impl test 3 failed";
  var r4 := GradeAllocation([0], 2);
  expect r4 == 0, "impl test 4 failed";
  var r5 := GradeAllocation([0], 5);
  expect r5 == 0, "impl test 5 failed";
  var r6 := GradeAllocation([0], 10);
  expect r6 == 0, "impl test 6 failed";
  var r7 := GradeAllocation([0], 50);
  expect r7 == 0, "impl test 7 failed";
  var r8 := GradeAllocation([0], 100);
  expect r8 == 0, "impl test 8 failed";
  var r9 := GradeAllocation([0], 500);
  expect r9 == 0, "impl test 9 failed";
  var r10 := GradeAllocation([0], 1000);
  expect r10 == 0, "impl test 10 failed";
  var r11 := GradeAllocation([0], 5000);
  expect r11 == 0, "impl test 11 failed";
  var r12 := GradeAllocation([0], 10000);
  expect r12 == 0, "impl test 12 failed";
  var r13 := GradeAllocation([0], 50000);
  expect r13 == 0, "impl test 13 failed";
  var r14 := GradeAllocation([0], 100000);
  expect r14 == 0, "impl test 14 failed";

  // Single student, nonzero score
  var r15 := GradeAllocation([4], 5);
  expect r15 == 4, "impl test 15 failed";
  var r16 := GradeAllocation([5], 5);
  expect r16 == 5, "impl test 16 failed";
  var r17 := GradeAllocation([9], 10);
  expect r17 == 9, "impl test 17 failed";
  var r18 := GradeAllocation([10], 10);
  expect r18 == 10, "impl test 18 failed";
  var r19 := GradeAllocation([9999], 100000);
  expect r19 == 9999, "impl test 19 failed";
  var r20 := GradeAllocation([100000], 100000);
  expect r20 == 100000, "impl test 20 failed";
  var r21 := GradeAllocation([386], 4999);
  expect r21 == 386, "impl test 21 failed";
  var r22 := GradeAllocation([1], 100000);
  expect r22 == 1, "impl test 22 failed";

  // Four students
  var r23 := GradeAllocation([1, 0, 0, 0], 5);
  expect r23 == 1, "impl test 23 failed";
  var r24 := GradeAllocation([0, 1, 0, 0], 5);
  expect r24 == 1, "impl test 24 failed";
  var r25 := GradeAllocation([0, 0, 0, 0], 5);
  expect r25 == 0, "impl test 25 failed";
  var r26 := GradeAllocation([5, 5, 5, 5], 5);
  expect r26 == 5, "impl test 26 failed";
  var r27 := GradeAllocation([4, 4, 5, 5], 5);
  expect r27 == 5, "impl test 27 failed";
  var r28 := GradeAllocation([5, 4, 4, 4], 5);
  expect r28 == 5, "impl test 28 failed";
  var r29 := GradeAllocation([4, 0, 0, 0], 5);
  expect r29 == 4, "impl test 29 failed";

  print "All tests passed\n";
}