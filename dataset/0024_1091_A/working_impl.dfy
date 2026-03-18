method MaxOrnaments(y: int, b: int, r: int) returns (total: int)
{
  var m := y;
  if b - 1 < m { m := b - 1; }
  if r - 2 < m { m := r - 2; }
  total := 3 * m + 3;
}

method Main()
{
  var result: int;

  result := MaxOrnaments(8, 13, 9);
  expect result == 24, "Test 1 failed";

  result := MaxOrnaments(13, 3, 6);
  expect result == 9, "Test 2 failed";

  result := MaxOrnaments(3, 8, 20);
  expect result == 12, "Test 3 failed";

  result := MaxOrnaments(1, 2, 3);
  expect result == 6, "Test 4 failed";

  result := MaxOrnaments(100, 100, 100);
  expect result == 297, "Test 5 failed";

  result := MaxOrnaments(9, 5, 5);
  expect result == 12, "Test 6 failed";

  result := MaxOrnaments(88, 89, 7);
  expect result == 18, "Test 7 failed";

  result := MaxOrnaments(50, 80, 70);
  expect result == 153, "Test 8 failed";

  result := MaxOrnaments(80, 81, 82);
  expect result == 243, "Test 9 failed";

  result := MaxOrnaments(100, 98, 99);
  expect result == 294, "Test 10 failed";

  result := MaxOrnaments(65, 69, 67);
  expect result == 198, "Test 11 failed";

  result := MaxOrnaments(55, 56, 76);
  expect result == 168, "Test 12 failed";

  result := MaxOrnaments(78, 3, 79);
  expect result == 9, "Test 13 failed";

  result := MaxOrnaments(4, 49, 50);
  expect result == 15, "Test 14 failed";

  result := MaxOrnaments(80, 90, 80);
  expect result == 237, "Test 15 failed";

  result := MaxOrnaments(40, 50, 50);
  expect result == 123, "Test 16 failed";

  result := MaxOrnaments(70, 70, 80);
  expect result == 210, "Test 17 failed";

  result := MaxOrnaments(50, 20, 50);
  expect result == 60, "Test 18 failed";

  result := MaxOrnaments(90, 56, 56);
  expect result == 165, "Test 19 failed";

  result := MaxOrnaments(66, 66, 37);
  expect result == 108, "Test 20 failed";

  print "All tests passed\n";
}