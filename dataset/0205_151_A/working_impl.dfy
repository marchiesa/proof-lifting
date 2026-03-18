method SoftDrinking(n: int, k: int, l: int, c: int, d: int, p: int, nl: int, np: int) returns (toasts: int)
{
  var totalDrink := k * l;
  var drinksPossible := totalDrink / nl;
  var limePieces := c * d;
  if limePieces < drinksPossible {
    drinksPossible := limePieces;
  }
  var saltServings := p / np;
  if saltServings < drinksPossible {
    drinksPossible := saltServings;
  }
  toasts := drinksPossible / n;
}

method Main()
{
  var r: int;

  r := SoftDrinking(3, 4, 5, 10, 8, 100, 3, 1);
  expect r == 2, "Test 1 failed";

  r := SoftDrinking(5, 100, 10, 1, 19, 90, 4, 3);
  expect r == 3, "Test 2 failed";

  r := SoftDrinking(10, 1000, 1000, 25, 23, 1, 50, 1);
  expect r == 0, "Test 3 failed";

  r := SoftDrinking(1, 7, 4, 5, 5, 8, 3, 2);
  expect r == 4, "Test 4 failed";

  r := SoftDrinking(2, 3, 3, 5, 5, 10, 1, 3);
  expect r == 1, "Test 5 failed";

  r := SoftDrinking(2, 6, 4, 5, 6, 5, 1, 3);
  expect r == 0, "Test 6 failed";

  r := SoftDrinking(1, 7, 3, 5, 3, 6, 2, 1);
  expect r == 6, "Test 7 failed";

  r := SoftDrinking(2, 4, 5, 4, 5, 7, 3, 2);
  expect r == 1, "Test 8 failed";

  r := SoftDrinking(2, 3, 6, 5, 7, 8, 2, 1);
  expect r == 4, "Test 9 failed";

  r := SoftDrinking(1, 4, 5, 5, 3, 10, 3, 1);
  expect r == 6, "Test 10 failed";

  r := SoftDrinking(1, 4, 6, 7, 3, 5, 1, 3);
  expect r == 1, "Test 11 failed";

  r := SoftDrinking(1, 6, 5, 5, 5, 8, 3, 1);
  expect r == 8, "Test 12 failed";

  r := SoftDrinking(1, 7, 5, 3, 3, 9, 2, 1);
  expect r == 9, "Test 13 failed";

  r := SoftDrinking(3, 5, 3, 7, 6, 10, 3, 1);
  expect r == 1, "Test 14 failed";

  r := SoftDrinking(3, 6, 3, 5, 3, 6, 3, 1);
  expect r == 2, "Test 15 failed";

  r := SoftDrinking(1, 7, 5, 5, 5, 5, 2, 2);
  expect r == 2, "Test 16 failed";

  r := SoftDrinking(2, 5, 3, 5, 6, 9, 2, 1);
  expect r == 3, "Test 17 failed";

  r := SoftDrinking(3, 4, 3, 5, 3, 6, 2, 1);
  expect r == 2, "Test 18 failed";

  r := SoftDrinking(1, 5, 5, 4, 7, 6, 3, 1);
  expect r == 6, "Test 19 failed";

  r := SoftDrinking(2, 3, 7, 6, 5, 9, 3, 1);
  expect r == 3, "Test 20 failed";

  print "All tests passed\n";
}