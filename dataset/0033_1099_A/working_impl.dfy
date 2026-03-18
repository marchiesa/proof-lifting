method Snowball(w: int, h: int, u1: int, d1: int, u2: int, d2: int) returns (finalWeight: int)
{
  finalWeight := w;
  var i := h;
  while i >= 0 {
    finalWeight := finalWeight + i;
    if i == d1 {
      finalWeight := finalWeight - u1;
      if finalWeight < 0 {
        finalWeight := 0;
      }
    }
    if i == d2 {
      finalWeight := finalWeight - u2;
      if finalWeight < 0 {
        finalWeight := 0;
      }
    }
    i := i - 1;
  }
}

method Main()
{
  var r: int;

  r := Snowball(4, 3, 1, 1, 1, 2);
  expect r == 8, "Test 1 failed";

  r := Snowball(4, 3, 9, 2, 0, 1);
  expect r == 1, "Test 2 failed";

  r := Snowball(41, 2, 1, 1, 67, 2);
  expect r == 0, "Test 3 failed";

  r := Snowball(87, 2, 10, 2, 76, 1);
  expect r == 4, "Test 4 failed";

  r := Snowball(94, 3, 71, 3, 12, 2);
  expect r == 17, "Test 5 failed";

  r := Snowball(30, 2, 88, 1, 2, 2);
  expect r == 0, "Test 6 failed";

  r := Snowball(8, 2, 29, 1, 23, 2);
  expect r == 0, "Test 7 failed";

  r := Snowball(85, 3, 47, 1, 92, 3);
  expect r == 0, "Test 8 failed";

  r := Snowball(34, 5, 82, 2, 52, 5);
  expect r == 1, "Test 9 failed";

  r := Snowball(19, 7, 14, 7, 28, 3);
  expect r == 5, "Test 10 failed";

  r := Snowball(43, 10, 72, 7, 49, 1);
  expect r == 0, "Test 11 failed";

  r := Snowball(94, 30, 83, 11, 85, 27);
  expect r == 391, "Test 12 failed";

  r := Snowball(19, 50, 36, 15, 90, 16);
  expect r == 1168, "Test 13 failed";

  r := Snowball(29, 100, 30, 51, 28, 92);
  expect r == 5021, "Test 14 failed";

  r := Snowball(71, 100, 56, 44, 12, 85);
  expect r == 5053, "Test 15 failed";

  r := Snowball(80, 7, 17, 4, 96, 3);
  expect r == 3, "Test 16 failed";

  r := Snowball(6, 10, 12, 5, 86, 4);
  expect r == 6, "Test 17 failed";

  r := Snowball(94, 80, 44, 14, 26, 7);
  expect r == 3264, "Test 18 failed";

  r := Snowball(24, 62, 24, 27, 48, 13);
  expect r == 1905, "Test 19 failed";

  r := Snowball(98, 68, 94, 39, 69, 19);
  expect r == 2281, "Test 20 failed";

  print "All tests passed\n";
}