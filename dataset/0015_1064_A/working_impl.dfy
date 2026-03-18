method MakeTriangle(a: int, b: int, c: int) returns (minutes: int)
{
  var m := a;
  if b > m { m := b; }
  if c > m { m := c; }
  var diff := m - a - b - c + m + 1;
  if diff < 0 { minutes := 0; } else { minutes := diff; }
}

method Main()
{
  var r1 := MakeTriangle(3, 4, 5);
  expect r1 == 0, "Test 1 failed";

  var r2 := MakeTriangle(2, 5, 3);
  expect r2 == 1, "Test 2 failed";

  var r3 := MakeTriangle(100, 10, 10);
  expect r3 == 81, "Test 3 failed";

  var r4 := MakeTriangle(1, 1, 1);
  expect r4 == 0, "Test 4 failed";

  var r5 := MakeTriangle(100, 100, 100);
  expect r5 == 0, "Test 5 failed";

  var r6 := MakeTriangle(100, 1, 1);
  expect r6 == 99, "Test 6 failed";

  var r7 := MakeTriangle(12, 34, 56);
  expect r7 == 11, "Test 7 failed";

  var r8 := MakeTriangle(68, 1, 67);
  expect r8 == 1, "Test 8 failed";

  var r9 := MakeTriangle(100, 100, 1);
  expect r9 == 0, "Test 9 failed";

  var r10 := MakeTriangle(100, 1, 99);
  expect r10 == 1, "Test 10 failed";

  var r11 := MakeTriangle(23, 56, 33);
  expect r11 == 1, "Test 11 failed";

  var r12 := MakeTriangle(98, 12, 23);
  expect r12 == 64, "Test 12 failed";

  var r13 := MakeTriangle(88, 2, 6);
  expect r13 == 81, "Test 13 failed";

  var r14 := MakeTriangle(1, 50, 87);
  expect r14 == 37, "Test 14 failed";

  var r15 := MakeTriangle(1, 50, 100);
  expect r15 == 50, "Test 15 failed";

  var r16 := MakeTriangle(1, 92, 13);
  expect r16 == 79, "Test 16 failed";

  var r17 := MakeTriangle(56, 42, 87);
  expect r17 == 0, "Test 17 failed";

  var r18 := MakeTriangle(100, 100, 99);
  expect r18 == 0, "Test 18 failed";

  var r19 := MakeTriangle(3, 1, 1);
  expect r19 == 2, "Test 19 failed";

  var r20 := MakeTriangle(14, 21, 76);
  expect r20 == 42, "Test 20 failed";

  print "All tests passed\n";
}