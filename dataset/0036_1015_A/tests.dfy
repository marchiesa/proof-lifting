predicate PointInSegment(p: int, seg: (int, int))
{
  seg.0 <= p <= seg.1
}

predicate PointCoveredByAny(p: int, segments: seq<(int, int)>)
{
  exists i | 0 <= i < |segments| :: PointInSegment(p, segments[i])
}

predicate StrictlyIncreasing(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
}

predicate MeetsSpec(segments: seq<(int, int)>, m: int, result: seq<int>)
{
  (forall i | 0 <= i < |result| :: 1 <= result[i] <= m) &&
  (forall i | 0 <= i < |result| :: !PointCoveredByAny(result[i], segments)) &&
  (forall p | 1 <= p <= m :: !PointCoveredByAny(p, segments) ==>
    (exists j | 0 <= j < |result| :: result[j] == p)) &&
  StrictlyIncreasing(result)
}

method PointsInSegments(segments: seq<(int, int)>, m: int) returns (result: seq<int>)
  requires m >= 0
  requires forall i | 0 <= i < |segments| :: 1 <= segments[i].0 <= segments[i].1 <= m
  ensures forall i | 0 <= i < |result| :: 1 <= result[i] <= m
  ensures forall i | 0 <= i < |result| :: !PointCoveredByAny(result[i], segments)
  ensures forall p | 1 <= p <= m :: !PointCoveredByAny(p, segments) ==>
    (exists j | 0 <= j < |result| :: result[j] == p)
  ensures StrictlyIncreasing(result)
{
  var A := seq(m, (_: int) => true);
  var i := 0;
  while i < |segments| {
    var a := segments[i].0;
    var b := segments[i].1;
    var j := a - 1;
    while j < b {
      if 0 <= j < |A| {
        A := A[j := false];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := [];
  var k := 0;
  while k < m {
    if A[k] {
      result := result + [k + 1];
    }
    k := k + 1;
  }
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // MeetsSpec should accept correct input/output pairs (small inputs)

  // SP1 (Test 1 scaled): covered={1,2,5}, uncovered={3,4}
  expect MeetsSpec([(2,2),(1,2),(5,5)], 5, [3,4]), "spec positive 1";

  // SP2 (Test 2 scaled): all points covered
  expect MeetsSpec([(1,3)], 3, []), "spec positive 2";

  // SP3 (Test 4 scaled): covered={2,3,4}, uncovered={1,5}
  expect MeetsSpec([(2,4)], 5, [1,5]), "spec positive 3";

  // SP4 (Test 5 scaled): covered={2}, uncovered={1}
  expect MeetsSpec([(2,2),(2,2)], 2, [1]), "spec positive 4";

  // SP5 (Test 6 scaled): covered={2}, uncovered={1,3}
  expect MeetsSpec([(2,2)], 3, [1,3]), "spec positive 5";

  // SP6 (Test 7 scaled): covered={3}, uncovered={1,2,4}
  expect MeetsSpec([(3,3)], 4, [1,2,4]), "spec positive 6";

  // SP7 (Test 8 scaled): covered={1,2,3}, uncovered={4}
  expect MeetsSpec([(3,3),(1,2)], 4, [4]), "spec positive 7";

  // SP8 (Test 9 scaled): all points covered
  expect MeetsSpec([(1,2),(2,3)], 3, []), "spec positive 8";

  // SP9 (Test 10 scaled): covered={1,3}, uncovered={2}
  expect MeetsSpec([(1,1),(3,3)], 3, [2]), "spec positive 9";

  // SP10 (Test 11): covered={1}, uncovered={2}
  expect MeetsSpec([(1,1)], 2, [2]), "spec positive 10";

  // SP11 (Test 12 scaled): covered={2,3}, uncovered={1}
  expect MeetsSpec([(2,2),(2,3),(3,3)], 3, [1]), "spec positive 11";

  // SP12 (Test 13 scaled): covered={1,2}, uncovered={3}
  expect MeetsSpec([(1,1),(1,1),(2,2)], 3, [3]), "spec positive 12";

  // SP13 (Test 14 scaled): all covered
  expect MeetsSpec([(1,1),(1,1)], 1, []), "spec positive 13";

  // ===== SPEC NEGATIVE TESTS =====
  // MeetsSpec should reject wrong outputs

  // SN1 (Neg 1 scaled): wrong includes covered point 2
  expect !MeetsSpec([(2,2),(1,2)], 3, [2,3]), "spec negative 1";

  // SN2 (Neg 2 scaled): wrong includes covered point 1
  expect !MeetsSpec([(1,3)], 3, [1]), "spec negative 2";

  // SN3 (Neg 3 scaled): wrong includes covered point 1
  expect !MeetsSpec([(1,2)], 4, [1,3,4]), "spec negative 3";

  // SN4 (Neg 4 scaled): wrong includes covered point 3
  expect !MeetsSpec([(2,4)], 5, [1,3,5]), "spec negative 4";

  // SN5 (Neg 5 scaled): wrong includes covered point 2
  expect !MeetsSpec([(2,2),(2,2)], 2, [1,2]), "spec negative 5";

  // SN6 (Neg 6 scaled): wrong includes covered point 2
  expect !MeetsSpec([(2,2)], 3, [1,2,3]), "spec negative 6";

  // SN7 (Neg 7 scaled): wrong is missing uncovered point 2 (completeness violation)
  expect !MeetsSpec([(3,3)], 4, [1,4]), "spec negative 7";

  // SN8 (Neg 8 scaled): wrong includes covered point 1
  expect !MeetsSpec([(3,3),(1,2)], 4, [1,4]), "spec negative 8";

  // SN9 (Neg 9 scaled): wrong includes covered point 1
  expect !MeetsSpec([(1,2),(2,3)], 3, [1]), "spec negative 9";

  // SN10 (Neg 10 scaled): wrong includes covered point 3
  expect !MeetsSpec([(1,1),(3,3)], 3, [2,3]), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====

  // Test 1
  var r1 := PointsInSegments([(2,2),(1,2),(5,5)], 5);
  expect r1 == [3,4], "impl test 1 failed";

  // Test 2
  var r2 := PointsInSegments([(1,7)], 7);
  expect r2 == [], "impl test 2 failed";

  // Test 3
  var seg3: seq<(int,int)> := [
    (1,2),(1,3),(1,3),(2,3),(1,1),(1,2),(1,1),(1,2),(1,3),(1,2),
    (1,2),(1,5),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,2),(1,1),
    (1,1),(1,2),(2,2),(1,1),(1,5),(1,4),(1,1),(2,2),(2,9),(1,1),
    (1,5),(2,3),(2,3),(1,5),(1,2),(2,2),(2,2),(1,2),(1,2),(3,4),
    (1,5),(1,1),(1,1),(1,1),(1,1),(2,2),(1,3),(1,2),(1,2),(1,2),
    (1,1),(2,2),(1,4),(1,3),(1,1),(1,2),(1,1),(2,3),(1,2),(2,2),
    (1,1),(1,5),(1,2),(2,2),(1,1),(1,1),(1,2),(1,4),(2,3),(1,2),
    (1,1),(2,2),(1,5),(1,1),(1,6),(1,1),(1,1),(1,2),(1,1),(1,4),
    (2,2),(1,1),(1,1),(1,2),(1,2),(1,2),(1,1),(1,2),(2,3),(1,1),
    (1,1),(1,3),(1,3),(1,2),(1,2),(1,1),(1,2),(1,2),(1,1),(1,2)
  ];
  var expected3 := seq(91, (i: int) => i + 10);
  var r3 := PointsInSegments(seg3, 100);
  expect r3 == expected3, "impl test 3 failed";

  // Test 4
  var r4 := PointsInSegments([(2,99)], 100);
  expect r4 == [1,100], "impl test 4 failed";

  // Test 5
  var seg5 := seq(100, (i: int) => (2, 2));
  var r5 := PointsInSegments(seg5, 2);
  expect r5 == [1], "impl test 5 failed";

  // Test 6
  var expected6 := seq(53, (i: int) => i + 1) + seq(46, (i: int) => i + 55);
  var r6 := PointsInSegments([(54,54)], 100);
  expect r6 == expected6, "impl test 6 failed";

  // Test 7
  var r7 := PointsInSegments([(5,5)], 7);
  expect r7 == [1,2,3,4,6,7], "impl test 7 failed";

  // Test 8
  var r8 := PointsInSegments([(9,9),(4,6)], 9);
  expect r8 == [1,2,3,7,8], "impl test 8 failed";

  // Test 9
  var r9 := PointsInSegments([(2,5),(9,11),(1,6),(5,6),(1,3),(2,7),(11,11),(9,10),(4,7),(5,9)], 11);
  expect r9 == [], "impl test 9 failed";

  // Test 10
  var r10 := PointsInSegments([(1,1),(3,4),(4,4),(5,5)], 5);
  expect r10 == [2], "impl test 10 failed";

  // Test 11
  var r11 := PointsInSegments([(1,1)], 2);
  expect r11 == [2], "impl test 11 failed";

  // Test 12
  var r12 := PointsInSegments([(4,4),(4,5),(5,5)], 5);
  expect r12 == [1,2,3], "impl test 12 failed";

  // Test 13
  var r13 := PointsInSegments([(1,1),(1,1),(1,1),(2,2)], 3);
  expect r13 == [3], "impl test 13 failed";

  // Test 14
  var seg14 := seq(26, (i: int) => (1, 1));
  var r14 := PointsInSegments(seg14, 1);
  expect r14 == [], "impl test 14 failed";

  print "All tests passed\n";
}