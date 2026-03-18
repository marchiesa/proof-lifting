method PointsInSegments(segments: seq<(int, int)>, m: int) returns (result: seq<int>)
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
  // Test 1
  var r1 := PointsInSegments([(2,2),(1,2),(5,5)], 5);
  expect r1 == [3,4], "Test 1 failed";

  // Test 2
  var r2 := PointsInSegments([(1,7)], 7);
  expect r2 == [], "Test 2 failed";

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
  expect r3 == expected3, "Test 3 failed";

  // Test 4
  var r4 := PointsInSegments([(2,99)], 100);
  expect r4 == [1,100], "Test 4 failed";

  // Test 5
  var seg5 := seq(100, (i: int) => (2, 2));
  var r5 := PointsInSegments(seg5, 2);
  expect r5 == [1], "Test 5 failed";

  // Test 6
  var expected6 := seq(53, (i: int) => i + 1) + seq(46, (i: int) => i + 55);
  var r6 := PointsInSegments([(54,54)], 100);
  expect r6 == expected6, "Test 6 failed";

  // Test 7
  var r7 := PointsInSegments([(5,5)], 7);
  expect r7 == [1,2,3,4,6,7], "Test 7 failed";

  // Test 8
  var r8 := PointsInSegments([(9,9),(4,6)], 9);
  expect r8 == [1,2,3,7,8], "Test 8 failed";

  // Test 9
  var r9 := PointsInSegments([(2,5),(9,11),(1,6),(5,6),(1,3),(2,7),(11,11),(9,10),(4,7),(5,9)], 11);
  expect r9 == [], "Test 9 failed";

  // Test 10
  var r10 := PointsInSegments([(1,1),(3,4),(4,4),(5,5)], 5);
  expect r10 == [2], "Test 10 failed";

  // Test 11
  var r11 := PointsInSegments([(1,1)], 2);
  expect r11 == [2], "Test 11 failed";

  // Test 12
  var r12 := PointsInSegments([(4,4),(4,5),(5,5)], 5);
  expect r12 == [1,2,3], "Test 12 failed";

  // Test 13
  var r13 := PointsInSegments([(1,1),(1,1),(1,1),(2,2)], 3);
  expect r13 == [3], "Test 13 failed";

  // Test 14
  var seg14 := seq(26, (i: int) => (1, 1));
  var r14 := PointsInSegments(seg14, 1);
  expect r14 == [], "Test 14 failed";

  print "All tests passed\n";
}