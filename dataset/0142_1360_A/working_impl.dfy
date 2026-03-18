method MinimalSquare(a: int, b: int) returns (area: int)
{
  var lo := if a < b then a else b;
  var hi := if a < b then b else a;
  var val := if 2 * lo > hi then 2 * lo else hi;
  area := val * val;
}

method Main()
{
  // Test 1
  var r1 := MinimalSquare(3, 2);
  expect r1 == 16, "Test (3,2) failed";
  var r2 := MinimalSquare(4, 2);
  expect r2 == 16, "Test (4,2) failed";
  var r3 := MinimalSquare(1, 1);
  expect r3 == 4, "Test (1,1) failed";
  var r4 := MinimalSquare(3, 1);
  expect r4 == 9, "Test (3,1) failed";
  var r5 := MinimalSquare(4, 7);
  expect r5 == 64, "Test (4,7) failed";
  var r6 := MinimalSquare(1, 3);
  expect r6 == 9, "Test (1,3) failed";
  var r7 := MinimalSquare(7, 4);
  expect r7 == 64, "Test (7,4) failed";
  var r8 := MinimalSquare(100, 100);
  expect r8 == 40000, "Test (100,100) failed";

  // Test 4
  var r9 := MinimalSquare(5, 5);
  expect r9 == 100, "Test (5,5) failed";

  // Test 5
  var r10 := MinimalSquare(2, 7);
  expect r10 == 49, "Test (2,7) failed";
  var r11 := MinimalSquare(4, 4);
  expect r11 == 64, "Test (4,4) failed";

  // Test 6
  var r12 := MinimalSquare(2, 1);
  expect r12 == 4, "Test (2,1) failed";
  var r13 := MinimalSquare(1, 2);
  expect r13 == 4, "Test (1,2) failed";
  var r14 := MinimalSquare(3, 3);
  expect r14 == 36, "Test (3,3) failed";
  var r15 := MinimalSquare(5, 3);
  expect r15 == 36, "Test (5,3) failed";

  // Test 8
  var r16 := MinimalSquare(6, 3);
  expect r16 == 36, "Test (6,3) failed";
  var r17 := MinimalSquare(3, 6);
  expect r17 == 36, "Test (3,6) failed";

  // Test 9
  var r18 := MinimalSquare(10, 5);
  expect r18 == 100, "Test (10,5) failed";
  var r19 := MinimalSquare(1, 50);
  expect r19 == 2500, "Test (1,50) failed";
  var r20 := MinimalSquare(25, 25);
  expect r20 == 2500, "Test (25,25) failed";
  var r21 := MinimalSquare(8, 3);
  expect r21 == 64, "Test (8,3) failed";

  // Test 11
  var r22 := MinimalSquare(50, 50);
  expect r22 == 10000, "Test (50,50) failed";
  var r23 := MinimalSquare(1, 49);
  expect r23 == 2401, "Test (1,49) failed";
  var r24 := MinimalSquare(30, 15);
  expect r24 == 900, "Test (30,15) failed";

  print "All tests passed\n";
}