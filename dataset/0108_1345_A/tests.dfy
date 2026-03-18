/*
 * Tests for Puzzle Pieces: spec predicates + implementation.
 */

function SideIsBlank(orientation: int, direction: int): bool
{
  orientation == direction
}

predicate ValidConfig(config: seq<int>, n: int, m: int)
  requires n >= 1 && m >= 1
{
  |config| == n * m &&
  (forall i | 0 <= i < n * m :: 0 <= config[i] <= 3)
}

predicate HorizEdgesOk(config: seq<int>, n: int, m: int)
  requires n >= 1 && m >= 1 && |config| == n * m
{
  forall r, c | 0 <= r < n && 0 <= c < m - 1 ::
    SideIsBlank(config[r * m + c], 1) != SideIsBlank(config[r * m + (c + 1)], 3)
}

predicate VertEdgesOk(config: seq<int>, n: int, m: int)
  requires n >= 1 && m >= 1 && |config| == n * m
{
  forall r, c | 0 <= r < n - 1 && 0 <= c < m ::
    SideIsBlank(config[r * m + c], 2) != SideIsBlank(config[(r + 1) * m + c], 0)
}

predicate IsSolution(config: seq<int>, n: int, m: int)
  requires n >= 1 && m >= 1
{
  ValidConfig(config, n, m) &&
  HorizEdgesOk(config, n, m) &&
  VertEdgesOk(config, n, m)
}

predicate HasSolutionFrom(n: int, m: int, partial: seq<int>)
  requires n >= 1 && m >= 1 && |partial| <= n * m
  decreases n * m - |partial|
{
  if |partial| == n * m then
    IsSolution(partial, n, m)
  else
    exists o | 0 <= o <= 3 :: HasSolutionFrom(n, m, partial + [o])
}

predicate PuzzleSolvable(n: int, m: int)
  requires n >= 1 && m >= 1
{
  HasSolutionFrom(n, m, [])
}

method PuzzlePieces(n: int, m: int) returns (result: bool)
  requires n >= 1 && m >= 1
  ensures result == PuzzleSolvable(n, m)
{
  result := n == 1 || m == 1 || (n == 2 && m == 2);
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Only small grids (up to 6 cells) to keep bounded-quantifier enumeration fast.

  // From Test 1: (1,3)->true
  expect PuzzleSolvable(1, 3) == true, "spec positive 1";
  // From Test 1: (2,2)->true
  expect PuzzleSolvable(2, 2) == true, "spec positive 2";
  // From Test 2: (1,1)->true
  expect PuzzleSolvable(1, 1) == true, "spec positive 3";
  // From Test 2: (1,2)->true
  expect PuzzleSolvable(1, 2) == true, "spec positive 4";
  // From Test 2: (2,1)->true
  expect PuzzleSolvable(2, 1) == true, "spec positive 5";
  // From Test 4: (1,4)->true
  expect PuzzleSolvable(1, 4) == true, "spec positive 6";
  // From Test 4: (4,1)->true
  expect PuzzleSolvable(4, 1) == true, "spec positive 7";
  // From Test 4: (2,3)->false
  expect PuzzleSolvable(2, 3) == false, "spec positive 8";
  // From Test 6: (3,1)->true
  expect PuzzleSolvable(3, 1) == true, "spec positive 9";
  // From Test 8: (3,2)->false
  expect PuzzleSolvable(3, 2) == false, "spec positive 10";
  // From Test 8: (1,5)->true
  expect PuzzleSolvable(1, 5) == true, "spec positive 11";
  // From Test 8: (5,1)->true
  expect PuzzleSolvable(5, 1) == true, "spec positive 12";

  // ===== SPEC NEGATIVE TESTS =====
  // Each tests that the spec rejects the wrong output for the given input.

  // From Neg 1: (2,2) correct=true, wrong=false
  expect PuzzleSolvable(2, 2) != false, "spec negative 1";
  // From Neg 3: (1,3) correct=true, wrong=false
  expect PuzzleSolvable(1, 3) != false, "spec negative 2";
  // From Neg 4: (2,3) correct=false, wrong=true
  expect PuzzleSolvable(2, 3) != true, "spec negative 3";
  // From Neg 6: (1,3) correct=true, wrong=false
  expect PuzzleSolvable(1, 3) != false, "spec negative 4";
  // From Neg 7: (1,1) correct=true, wrong=false
  expect PuzzleSolvable(1, 1) != false, "spec negative 5";
  // From Neg 5: (5,5) scaled to (2,3), correct=false, wrong=true
  expect PuzzleSolvable(2, 3) != true, "spec negative 6";
  // From Neg 8: (7,6) scaled to (3,2), correct=false, wrong=true
  expect PuzzleSolvable(3, 2) != true, "spec negative 7";
  // From Neg 9: (50,50) scaled to (2,3), correct=false, wrong=true
  expect PuzzleSolvable(2, 3) != true, "spec negative 8";
  // From Neg 10: (50,50) scaled to (3,2), correct=false, wrong=true
  expect PuzzleSolvable(3, 2) != true, "spec negative 9";
  // From Neg 2: (3,3) scaled to (3,2), correct=false, wrong=true
  expect PuzzleSolvable(3, 2) != true, "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  var r: bool;

  // Test 1
  r := PuzzlePieces(1, 3);
  expect r == true, "impl test 1.1 failed";
  r := PuzzlePieces(100000, 100000);
  expect r == false, "impl test 1.2 failed";
  r := PuzzlePieces(2, 2);
  expect r == true, "impl test 1.3 failed";

  // Test 2
  r := PuzzlePieces(1, 1);
  expect r == true, "impl test 2.1 failed";
  r := PuzzlePieces(1, 2);
  expect r == true, "impl test 2.2 failed";
  r := PuzzlePieces(2, 1);
  expect r == true, "impl test 2.3 failed";
  r := PuzzlePieces(2, 2);
  expect r == true, "impl test 2.4 failed";
  r := PuzzlePieces(3, 3);
  expect r == false, "impl test 2.5 failed";

  // Test 3
  r := PuzzlePieces(1, 3);
  expect r == true, "impl test 3.1 failed";

  // Test 4
  r := PuzzlePieces(1, 1);
  expect r == true, "impl test 4.1 failed";
  r := PuzzlePieces(1, 4);
  expect r == true, "impl test 4.2 failed";
  r := PuzzlePieces(4, 1);
  expect r == true, "impl test 4.3 failed";
  r := PuzzlePieces(2, 3);
  expect r == false, "impl test 4.4 failed";

  // Test 5
  r := PuzzlePieces(2, 2);
  expect r == true, "impl test 5.1 failed";
  r := PuzzlePieces(3, 4);
  expect r == false, "impl test 5.2 failed";
  r := PuzzlePieces(5, 5);
  expect r == false, "impl test 5.3 failed";

  // Test 6
  r := PuzzlePieces(1, 1);
  expect r == true, "impl test 6.1 failed";
  r := PuzzlePieces(1, 1);
  expect r == true, "impl test 6.2 failed";
  r := PuzzlePieces(2, 1);
  expect r == true, "impl test 6.3 failed";
  r := PuzzlePieces(1, 2);
  expect r == true, "impl test 6.4 failed";
  r := PuzzlePieces(3, 1);
  expect r == true, "impl test 6.5 failed";
  r := PuzzlePieces(1, 3);
  expect r == true, "impl test 6.6 failed";

  // Test 7
  r := PuzzlePieces(1, 1);
  expect r == true, "impl test 7.1 failed";

  // Test 8
  r := PuzzlePieces(4, 4);
  expect r == false, "impl test 8.1 failed";
  r := PuzzlePieces(3, 2);
  expect r == false, "impl test 8.2 failed";
  r := PuzzlePieces(2, 3);
  expect r == false, "impl test 8.3 failed";
  r := PuzzlePieces(5, 1);
  expect r == true, "impl test 8.4 failed";
  r := PuzzlePieces(1, 5);
  expect r == true, "impl test 8.5 failed";
  r := PuzzlePieces(6, 7);
  expect r == false, "impl test 8.6 failed";
  r := PuzzlePieces(7, 6);
  expect r == false, "impl test 8.7 failed";

  // Test 9
  r := PuzzlePieces(1, 1);
  expect r == true, "impl test 9.1 failed";
  r := PuzzlePieces(2, 2);
  expect r == true, "impl test 9.2 failed";
  r := PuzzlePieces(3, 3);
  expect r == false, "impl test 9.3 failed";
  r := PuzzlePieces(4, 4);
  expect r == false, "impl test 9.4 failed";
  r := PuzzlePieces(5, 5);
  expect r == false, "impl test 9.5 failed";
  r := PuzzlePieces(1, 10);
  expect r == true, "impl test 9.6 failed";
  r := PuzzlePieces(10, 1);
  expect r == true, "impl test 9.7 failed";
  r := PuzzlePieces(2, 5);
  expect r == false, "impl test 9.8 failed";
  r := PuzzlePieces(5, 2);
  expect r == false, "impl test 9.9 failed";
  r := PuzzlePieces(50, 50);
  expect r == false, "impl test 9.10 failed";

  // Test 10
  r := PuzzlePieces(1, 50);
  expect r == true, "impl test 10.1 failed";
  r := PuzzlePieces(50, 1);
  expect r == true, "impl test 10.2 failed";
  r := PuzzlePieces(50, 50);
  expect r == false, "impl test 10.3 failed";

  // Test 11
  r := PuzzlePieces(1, 1);
  expect r == true, "impl test 11.1 failed";
  r := PuzzlePieces(1, 2);
  expect r == true, "impl test 11.2 failed";
  r := PuzzlePieces(2, 1);
  expect r == true, "impl test 11.3 failed";
  r := PuzzlePieces(1, 3);
  expect r == true, "impl test 11.4 failed";
  r := PuzzlePieces(3, 1);
  expect r == true, "impl test 11.5 failed";
  r := PuzzlePieces(2, 4);
  expect r == false, "impl test 11.6 failed";
  r := PuzzlePieces(4, 2);
  expect r == false, "impl test 11.7 failed";
  r := PuzzlePieces(3, 5);
  expect r == false, "impl test 11.8 failed";

  print "All tests passed\n";
}