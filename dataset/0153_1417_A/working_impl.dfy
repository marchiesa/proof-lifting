method CopyPaste(n: int, k: int, a: seq<int>) returns (maxSpells: int)
{
  var m := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < m {
      m := a[i];
    }
    i := i + 1;
  }

  var out := 0;
  i := 0;
  while i < |a|
  {
    out := out + (k - a[i]) / m;
    i := i + 1;
  }

  out := out - (k - m) / m;
  return out;
}

method Main()
{
  // Test 1 (sub-cases from multi-test input)
  var r1 := CopyPaste(2, 2, [1, 1]);
  expect r1 == 1, "Test 1a failed";

  var r2 := CopyPaste(3, 5, [1, 2, 3]);
  expect r2 == 5, "Test 1b failed";

  var r3 := CopyPaste(3, 7, [3, 2, 2]);
  expect r3 == 4, "Test 1c failed";

  // Test 2
  var r4 := CopyPaste(2, 2, [1, 1]);
  expect r4 == 1, "Test 2 failed";

  // Test 3
  var r5 := CopyPaste(2, 10, [1, 1]);
  expect r5 == 9, "Test 3 failed";

  // Test 4
  var r6 := CopyPaste(3, 5, [1, 2, 3]);
  expect r6 == 5, "Test 4 failed";

  // Test 5
  var r7 := CopyPaste(4, 8, [2, 2, 2, 2]);
  expect r7 == 9, "Test 5 failed";

  // Test 6
  var r8 := CopyPaste(2, 50, [1, 49]);
  expect r8 == 1, "Test 6 failed";

  // Test 7
  var r9 := CopyPaste(5, 10, [1, 1, 1, 1, 1]);
  expect r9 == 36, "Test 7 failed";

  // Test 8
  var r10 := CopyPaste(3, 7, [3, 2, 2]);
  expect r10 == 4, "Test 8 failed";

  // Test 9
  var r11 := CopyPaste(2, 4, [2, 2]);
  expect r11 == 1, "Test 9 failed";

  // Test 10
  var r12 := CopyPaste(6, 12, [1, 2, 3, 4, 5, 6]);
  expect r12 == 40, "Test 10 failed";

  // Test 11 (sub-cases from multi-test input)
  var r13 := CopyPaste(2, 3, [1, 2]);
  expect r13 == 1, "Test 11a failed";

  var r14 := CopyPaste(3, 6, [1, 1, 1]);
  expect r14 == 10, "Test 11b failed";

  print "All tests passed\n";
}