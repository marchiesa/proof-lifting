method TwoRegularPolygons(t: int, cases: seq<(int, int)>) returns (results: seq<bool>)
{
  results := [];
  var i := 0;
  while i < |cases| {
    var (a, b) := cases[i];
    results := results + [a % b == 0];
    i := i + 1;
  }
}

method Main()
{
  // Test 1
  var r1 := TwoRegularPolygons(2, [(6, 3), (7, 3)]);
  expect r1 == [true, false], "Test 1 failed";

  // Test 2
  var r2 := TwoRegularPolygons(1, [(69, 68)]);
  expect r2 == [false], "Test 2 failed";

  // Test 3
  var r3 := TwoRegularPolygons(2, [(69, 68), (11, 9)]);
  expect r3 == [false, false], "Test 3 failed";

  // Test 4
  var r4 := TwoRegularPolygons(1, [(6, 3)]);
  expect r4 == [true], "Test 4 failed";

  // Test 5
  var r5 := TwoRegularPolygons(1, [(7, 3)]);
  expect r5 == [false], "Test 5 failed";

  // Test 6
  var r6 := TwoRegularPolygons(3, [(12, 4), (12, 3), (12, 6)]);
  expect r6 == [true, true, true], "Test 6 failed";

  // Test 7
  var r7 := TwoRegularPolygons(5, [(10, 5), (8, 4), (9, 3), (15, 5), (20, 4)]);
  expect r7 == [true, true, true, true, true], "Test 7 failed";

  // Test 8
  var r8 := TwoRegularPolygons(1, [(4, 3)]);
  expect r8 == [false], "Test 8 failed";

  // Test 9
  var r9 := TwoRegularPolygons(2, [(50, 25), (50, 10)]);
  expect r9 == [true, true], "Test 9 failed";

  // Test 10
  var r10 := TwoRegularPolygons(4, [(6, 4), (6, 5), (8, 3), (9, 6)]);
  expect r10 == [false, false, false, false], "Test 10 failed";

  // Test 11
  var r11 := TwoRegularPolygons(3, [(30, 5), (30, 6), (30, 10)]);
  expect r11 == [true, true, true], "Test 11 failed";

  // Test 12
  var r12 := TwoRegularPolygons(1, [(3, 3)]);
  expect r12 == [true], "Test 12 failed";

  // Test 13
  var r13 := TwoRegularPolygons(6, [(48, 3), (48, 4), (48, 6), (48, 8), (48, 12), (48, 16)]);
  expect r13 == [true, true, true, true, true, true], "Test 13 failed";

  print "All tests passed\n";
}