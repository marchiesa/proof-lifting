method TheDoors(n: int, doors: seq<int>) returns (k: int)
{
  var a := 0;
  var b := 0;
  var i := 0;
  while i < n {
    if doors[i] == 0 {
      a := a + 1;
    } else {
      b := b + 1;
    }
    i := i + 1;
  }
  var x := 0;
  var y := 0;
  i := 0;
  while i < n {
    if doors[i] == 1 {
      y := y + 1;
    } else {
      x := x + 1;
    }
    if x == a || y == b {
      return i + 1;
    }
    i := i + 1;
  }
  return 0;
}

method Main()
{
  // Test 1
  var r1 := TheDoors(5, [0, 0, 1, 0, 0]);
  expect r1 == 3, "Test 1 failed";

  // Test 2
  var r2 := TheDoors(4, [1, 0, 0, 1]);
  expect r2 == 3, "Test 2 failed";

  // Test 3
  var r3 := TheDoors(5, [1, 1, 0, 0, 0]);
  expect r3 == 2, "Test 3 failed";

  // Test 4
  var r4 := TheDoors(3, [0, 1, 0]);
  expect r4 == 2, "Test 4 failed";

  // Test 5
  var r5 := TheDoors(16, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]);
  expect r5 == 15, "Test 5 failed";

  // Test 6
  var r6 := TheDoors(250, [1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1]);
  expect r6 == 249, "Test 6 failed";

  // Test 7
  var r7 := TheDoors(2, [1, 0]);
  expect r7 == 1, "Test 7 failed";

  // Test 8
  var r8 := TheDoors(2, [0, 1]);
  expect r8 == 1, "Test 8 failed";

  // Test 9
  var r9 := TheDoors(3, [0, 0, 1]);
  expect r9 == 2, "Test 9 failed";

  // Test 10
  var r10 := TheDoors(3, [0, 1, 1]);
  expect r10 == 1, "Test 10 failed";

  // Test 11
  var r11 := TheDoors(3, [1, 0, 0]);
  expect r11 == 1, "Test 11 failed";

  // Test 12
  var r12 := TheDoors(3, [1, 0, 1]);
  expect r12 == 2, "Test 12 failed";

  // Test 13
  var r13 := TheDoors(3, [1, 1, 0]);
  expect r13 == 2, "Test 13 failed";

  print "All tests passed\n";
}