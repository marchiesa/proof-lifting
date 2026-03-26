method BoxIsPull(x1: int, y1: int, x2: int, y2: int) returns (time: int)
{
  var dx := if x1 > x2 then x1 - x2 else x2 - x1;
  var dy := if y1 > y2 then y1 - y2 else y2 - y1;
  if x1 == x2 {
    time := dy;
  } else if y1 == y2 {
    time := dx;
  } else {
    time := dx + dy + 2;
  }
}

method Main()
{
  // Test 1
  var r1 := BoxIsPull(1, 2, 2, 2);
  expect r1 == 1, "Test 1a failed";

  var r2 := BoxIsPull(1, 1, 2, 2);
  expect r2 == 4, "Test 1b failed";

  // Test 2
  var r3 := BoxIsPull(69, 69, 69, 69);
  expect r3 == 0, "Test 2 failed";

  // Test 3
  var r4 := BoxIsPull(1, 1, 1000000000, 1000000000);
  expect r4 == 2000000000, "Test 3a failed";

  var r5 := BoxIsPull(1, 1, 1000000000, 1000000000);
  expect r5 == 2000000000, "Test 3b failed";

  var r6 := BoxIsPull(1, 1, 1000000000, 1000000000);
  expect r6 == 2000000000, "Test 3c failed";

  var r7 := BoxIsPull(1, 1, 1000000000, 1000000000);
  expect r7 == 2000000000, "Test 3d failed";

  var r8 := BoxIsPull(1, 1, 65537, 65537);
  expect r8 == 131074, "Test 3e failed";

  // Test 4
  var r9 := BoxIsPull(1, 1, 131073, 131073);
  expect r9 == 262146, "Test 4 failed";

  // Test 5
  var r10 := BoxIsPull(3, 2, 4, 7);
  expect r10 == 8, "Test 5 failed";

  print "All tests passed\n";
}