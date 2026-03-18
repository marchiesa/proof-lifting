method PuzzlePieces(n: int, m: int) returns (result: bool)
{
  result := n == 1 || m == 1 || (n == 2 && m == 2);
}

method Main()
{
  // Test 1
  var r := PuzzlePieces(1, 3);
  expect r == true, "Test 1.1: PuzzlePieces(1, 3) failed";
  r := PuzzlePieces(100000, 100000);
  expect r == false, "Test 1.2: PuzzlePieces(100000, 100000) failed";
  r := PuzzlePieces(2, 2);
  expect r == true, "Test 1.3: PuzzlePieces(2, 2) failed";

  // Test 2
  r := PuzzlePieces(1, 1);
  expect r == true, "Test 2.1: PuzzlePieces(1, 1) failed";
  r := PuzzlePieces(1, 2);
  expect r == true, "Test 2.2: PuzzlePieces(1, 2) failed";
  r := PuzzlePieces(2, 1);
  expect r == true, "Test 2.3: PuzzlePieces(2, 1) failed";
  r := PuzzlePieces(2, 2);
  expect r == true, "Test 2.4: PuzzlePieces(2, 2) failed";
  r := PuzzlePieces(3, 3);
  expect r == false, "Test 2.5: PuzzlePieces(3, 3) failed";

  // Test 3
  r := PuzzlePieces(1, 3);
  expect r == true, "Test 3.1: PuzzlePieces(1, 3) failed";

  // Test 4
  r := PuzzlePieces(1, 1);
  expect r == true, "Test 4.1: PuzzlePieces(1, 1) failed";
  r := PuzzlePieces(1, 4);
  expect r == true, "Test 4.2: PuzzlePieces(1, 4) failed";
  r := PuzzlePieces(4, 1);
  expect r == true, "Test 4.3: PuzzlePieces(4, 1) failed";
  r := PuzzlePieces(2, 3);
  expect r == false, "Test 4.4: PuzzlePieces(2, 3) failed";

  // Test 5
  r := PuzzlePieces(2, 2);
  expect r == true, "Test 5.1: PuzzlePieces(2, 2) failed";
  r := PuzzlePieces(3, 4);
  expect r == false, "Test 5.2: PuzzlePieces(3, 4) failed";
  r := PuzzlePieces(5, 5);
  expect r == false, "Test 5.3: PuzzlePieces(5, 5) failed";

  // Test 6
  r := PuzzlePieces(1, 1);
  expect r == true, "Test 6.1: PuzzlePieces(1, 1) failed";
  r := PuzzlePieces(1, 1);
  expect r == true, "Test 6.2: PuzzlePieces(1, 1) failed";
  r := PuzzlePieces(2, 1);
  expect r == true, "Test 6.3: PuzzlePieces(2, 1) failed";
  r := PuzzlePieces(1, 2);
  expect r == true, "Test 6.4: PuzzlePieces(1, 2) failed";
  r := PuzzlePieces(3, 1);
  expect r == true, "Test 6.5: PuzzlePieces(3, 1) failed";
  r := PuzzlePieces(1, 3);
  expect r == true, "Test 6.6: PuzzlePieces(1, 3) failed";

  // Test 7
  r := PuzzlePieces(1, 1);
  expect r == true, "Test 7.1: PuzzlePieces(1, 1) failed";

  // Test 8
  r := PuzzlePieces(4, 4);
  expect r == false, "Test 8.1: PuzzlePieces(4, 4) failed";
  r := PuzzlePieces(3, 2);
  expect r == false, "Test 8.2: PuzzlePieces(3, 2) failed";
  r := PuzzlePieces(2, 3);
  expect r == false, "Test 8.3: PuzzlePieces(2, 3) failed";
  r := PuzzlePieces(5, 1);
  expect r == true, "Test 8.4: PuzzlePieces(5, 1) failed";
  r := PuzzlePieces(1, 5);
  expect r == true, "Test 8.5: PuzzlePieces(1, 5) failed";
  r := PuzzlePieces(6, 7);
  expect r == false, "Test 8.6: PuzzlePieces(6, 7) failed";
  r := PuzzlePieces(7, 6);
  expect r == false, "Test 8.7: PuzzlePieces(7, 6) failed";

  // Test 9
  r := PuzzlePieces(1, 1);
  expect r == true, "Test 9.1: PuzzlePieces(1, 1) failed";
  r := PuzzlePieces(2, 2);
  expect r == true, "Test 9.2: PuzzlePieces(2, 2) failed";
  r := PuzzlePieces(3, 3);
  expect r == false, "Test 9.3: PuzzlePieces(3, 3) failed";
  r := PuzzlePieces(4, 4);
  expect r == false, "Test 9.4: PuzzlePieces(4, 4) failed";
  r := PuzzlePieces(5, 5);
  expect r == false, "Test 9.5: PuzzlePieces(5, 5) failed";
  r := PuzzlePieces(1, 10);
  expect r == true, "Test 9.6: PuzzlePieces(1, 10) failed";
  r := PuzzlePieces(10, 1);
  expect r == true, "Test 9.7: PuzzlePieces(10, 1) failed";
  r := PuzzlePieces(2, 5);
  expect r == false, "Test 9.8: PuzzlePieces(2, 5) failed";
  r := PuzzlePieces(5, 2);
  expect r == false, "Test 9.9: PuzzlePieces(5, 2) failed";
  r := PuzzlePieces(50, 50);
  expect r == false, "Test 9.10: PuzzlePieces(50, 50) failed";

  // Test 10
  r := PuzzlePieces(1, 50);
  expect r == true, "Test 10.1: PuzzlePieces(1, 50) failed";
  r := PuzzlePieces(50, 1);
  expect r == true, "Test 10.2: PuzzlePieces(50, 1) failed";
  r := PuzzlePieces(50, 50);
  expect r == false, "Test 10.3: PuzzlePieces(50, 50) failed";

  // Test 11
  r := PuzzlePieces(1, 1);
  expect r == true, "Test 11.1: PuzzlePieces(1, 1) failed";
  r := PuzzlePieces(1, 2);
  expect r == true, "Test 11.2: PuzzlePieces(1, 2) failed";
  r := PuzzlePieces(2, 1);
  expect r == true, "Test 11.3: PuzzlePieces(2, 1) failed";
  r := PuzzlePieces(1, 3);
  expect r == true, "Test 11.4: PuzzlePieces(1, 3) failed";
  r := PuzzlePieces(3, 1);
  expect r == true, "Test 11.5: PuzzlePieces(3, 1) failed";
  r := PuzzlePieces(2, 4);
  expect r == false, "Test 11.6: PuzzlePieces(2, 4) failed";
  r := PuzzlePieces(4, 2);
  expect r == false, "Test 11.7: PuzzlePieces(4, 2) failed";
  r := PuzzlePieces(3, 5);
  expect r == false, "Test 11.8: PuzzlePieces(3, 5) failed";

  print "All tests passed\n";
}