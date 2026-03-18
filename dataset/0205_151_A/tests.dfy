predicate Feasible(n: int, k: int, l: int, c: int, d: int, p: int, nl: int, np: int, t: int)
{
  t >= 0 &&
  n * t * nl <= k * l &&
  n * t <= c * d &&
  n * t * np <= p
}

method SoftDrinking(n: int, k: int, l: int, c: int, d: int, p: int, nl: int, np: int) returns (toasts: int)
  requires n >= 1
  requires k >= 0 && l >= 0
  requires c >= 0 && d >= 0
  requires p >= 0
  requires nl >= 1
  requires np >= 1
  ensures Feasible(n, k, l, c, d, p, nl, np, toasts)
  ensures !Feasible(n, k, l, c, d, p, nl, np, toasts + 1)
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
  // ===== SPEC POSITIVE TESTS =====
  // Test both ensures: Feasible(..., correct) AND !Feasible(..., correct+1)

  expect Feasible(3, 4, 5, 10, 8, 100, 3, 1, 2), "spec pos 1a";
  expect !Feasible(3, 4, 5, 10, 8, 100, 3, 1, 3), "spec pos 1b";

  expect Feasible(5, 100, 10, 1, 19, 90, 4, 3, 3), "spec pos 2a";
  expect !Feasible(5, 100, 10, 1, 19, 90, 4, 3, 4), "spec pos 2b";

  expect Feasible(10, 1000, 1000, 25, 23, 1, 50, 1, 0), "spec pos 3a";
  expect !Feasible(10, 1000, 1000, 25, 23, 1, 50, 1, 1), "spec pos 3b";

  expect Feasible(1, 7, 4, 5, 5, 8, 3, 2, 4), "spec pos 4a";
  expect !Feasible(1, 7, 4, 5, 5, 8, 3, 2, 5), "spec pos 4b";

  expect Feasible(2, 3, 3, 5, 5, 10, 1, 3, 1), "spec pos 5a";
  expect !Feasible(2, 3, 3, 5, 5, 10, 1, 3, 2), "spec pos 5b";

  expect Feasible(2, 6, 4, 5, 6, 5, 1, 3, 0), "spec pos 6a";
  expect !Feasible(2, 6, 4, 5, 6, 5, 1, 3, 1), "spec pos 6b";

  expect Feasible(1, 7, 3, 5, 3, 6, 2, 1, 6), "spec pos 7a";
  expect !Feasible(1, 7, 3, 5, 3, 6, 2, 1, 7), "spec pos 7b";

  expect Feasible(2, 4, 5, 4, 5, 7, 3, 2, 1), "spec pos 8a";
  expect !Feasible(2, 4, 5, 4, 5, 7, 3, 2, 2), "spec pos 8b";

  expect Feasible(2, 3, 6, 5, 7, 8, 2, 1, 4), "spec pos 9a";
  expect !Feasible(2, 3, 6, 5, 7, 8, 2, 1, 5), "spec pos 9b";

  expect Feasible(1, 4, 5, 5, 3, 10, 3, 1, 6), "spec pos 10a";
  expect !Feasible(1, 4, 5, 5, 3, 10, 3, 1, 7), "spec pos 10b";

  // ===== SPEC NEGATIVE TESTS =====
  // Wrong outputs should NOT be feasible (they are all correct+1)

  expect !Feasible(3, 4, 5, 10, 8, 100, 3, 1, 3), "spec neg 1";
  expect !Feasible(5, 100, 10, 1, 19, 90, 4, 3, 4), "spec neg 2";
  expect !Feasible(10, 1000, 1000, 25, 23, 1, 50, 1, 1), "spec neg 3";
  expect !Feasible(1, 7, 4, 5, 5, 8, 3, 2, 5), "spec neg 4";
  expect !Feasible(2, 3, 3, 5, 5, 10, 1, 3, 2), "spec neg 5";
  expect !Feasible(2, 6, 4, 5, 6, 5, 1, 3, 1), "spec neg 6";
  expect !Feasible(1, 7, 3, 5, 3, 6, 2, 1, 7), "spec neg 7";
  expect !Feasible(2, 4, 5, 4, 5, 7, 3, 2, 2), "spec neg 8";
  expect !Feasible(2, 3, 6, 5, 7, 8, 2, 1, 5), "spec neg 9";
  expect !Feasible(1, 4, 5, 5, 3, 10, 3, 1, 7), "spec neg 10";

  // ===== IMPLEMENTATION TESTS =====

  var r: int;

  r := SoftDrinking(3, 4, 5, 10, 8, 100, 3, 1);
  expect r == 2, "impl test 1 failed";

  r := SoftDrinking(5, 100, 10, 1, 19, 90, 4, 3);
  expect r == 3, "impl test 2 failed";

  r := SoftDrinking(10, 1000, 1000, 25, 23, 1, 50, 1);
  expect r == 0, "impl test 3 failed";

  r := SoftDrinking(1, 7, 4, 5, 5, 8, 3, 2);
  expect r == 4, "impl test 4 failed";

  r := SoftDrinking(2, 3, 3, 5, 5, 10, 1, 3);
  expect r == 1, "impl test 5 failed";

  r := SoftDrinking(2, 6, 4, 5, 6, 5, 1, 3);
  expect r == 0, "impl test 6 failed";

  r := SoftDrinking(1, 7, 3, 5, 3, 6, 2, 1);
  expect r == 6, "impl test 7 failed";

  r := SoftDrinking(2, 4, 5, 4, 5, 7, 3, 2);
  expect r == 1, "impl test 8 failed";

  r := SoftDrinking(2, 3, 6, 5, 7, 8, 2, 1);
  expect r == 4, "impl test 9 failed";

  r := SoftDrinking(1, 4, 5, 5, 3, 10, 3, 1);
  expect r == 6, "impl test 10 failed";

  r := SoftDrinking(1, 4, 6, 7, 3, 5, 1, 3);
  expect r == 1, "impl test 11 failed";

  r := SoftDrinking(1, 6, 5, 5, 5, 8, 3, 1);
  expect r == 8, "impl test 12 failed";

  r := SoftDrinking(1, 7, 5, 3, 3, 9, 2, 1);
  expect r == 9, "impl test 13 failed";

  r := SoftDrinking(3, 5, 3, 7, 6, 10, 3, 1);
  expect r == 1, "impl test 14 failed";

  r := SoftDrinking(3, 6, 3, 5, 3, 6, 3, 1);
  expect r == 2, "impl test 15 failed";

  r := SoftDrinking(1, 7, 5, 5, 5, 5, 2, 2);
  expect r == 2, "impl test 16 failed";

  r := SoftDrinking(2, 5, 3, 5, 6, 9, 2, 1);
  expect r == 3, "impl test 17 failed";

  r := SoftDrinking(3, 4, 3, 5, 3, 6, 2, 1);
  expect r == 2, "impl test 18 failed";

  r := SoftDrinking(1, 5, 5, 4, 7, 6, 3, 1);
  expect r == 6, "impl test 19 failed";

  r := SoftDrinking(2, 3, 7, 6, 5, 9, 3, 1);
  expect r == 3, "impl test 20 failed";

  print "All tests passed\n";
}