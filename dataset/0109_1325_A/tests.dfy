function Min(a: int, b: int): int {
  if a <= b then a else b
}

function Max(a: int, b: int): int {
  if a >= b then a else b
}

predicate Divides(d: int, n: int)
  requires d > 0
{
  n % d == 0
}

predicate IsGcd(g: int, a: int, b: int)
  requires a > 0 && b > 0 && g > 0
{
  Divides(g, a) && Divides(g, b) &&
  forall d | 1 <= d <= Min(a, b) :: (Divides(d, a) && Divides(d, b)) ==> d <= g
}

predicate IsLcm(l: int, a: int, b: int)
  requires a > 0 && b > 0 && l > 0
{
  Divides(a, l) && Divides(b, l) &&
  forall m | 1 <= m <= l :: (Divides(a, m) && Divides(b, m)) ==> l <= m
}

predicate ValidSolution(a: int, b: int, x: int)
{
  a > 0 && b > 0 && x > 0 &&
  exists g | 1 <= g <= Min(a, b) ::
    exists l | Max(a, b) <= l <= a * b ::
      IsGcd(g, a, b) && IsLcm(l, a, b) && g + l == x
}

method EhAbAndGcd(x: int) returns (a: int, b: int)
  requires x >= 2
  ensures ValidSolution(a, b, x)
{
  a := 1;
  b := x - 1;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  expect ValidSolution(1, 1, 2), "spec positive 1";   // x=2
  expect ValidSolution(1, 2, 3), "spec positive 2";   // x=3
  expect ValidSolution(1, 3, 4), "spec positive 3";   // x=4
  expect ValidSolution(1, 4, 5), "spec positive 4";   // x=5
  expect ValidSolution(1, 6, 7), "spec positive 5";   // x=7
  expect ValidSolution(1, 9, 10), "spec positive 6";  // x=10
  expect ValidSolution(1, 13, 14), "spec positive 7"; // x=14
  expect ValidSolution(1, 24, 25), "spec positive 8"; // x=25

  // ===== SPEC NEGATIVE TESTS =====
  expect !ValidSolution(2, 1, 2), "spec negative 1";   // x=2, wrong a=2
  expect !ValidSolution(2, 2, 3), "spec negative 2";   // x=3, wrong a=2
  expect !ValidSolution(2, 3, 4), "spec negative 3";   // x=4, wrong a=2
  expect !ValidSolution(2, 6, 7), "spec negative 4";   // x=7, wrong a=2
  expect !ValidSolution(2, 9, 10), "spec negative 5";  // x=10, wrong a=2
  expect !ValidSolution(2, 13, 14), "spec negative 6"; // x=14, wrong a=2
  expect !ValidSolution(2, 24, 25), "spec negative 7"; // x=25, wrong a=2
  expect !ValidSolution(2, 49, 50), "spec negative 8"; // x=50, wrong a=2

  // ===== IMPLEMENTATION TESTS =====
  var a: int, b: int;

  a, b := EhAbAndGcd(2);
  expect a == 1 && b == 1, "impl test: x=2";

  a, b := EhAbAndGcd(3);
  expect a == 1 && b == 2, "impl test: x=3";

  a, b := EhAbAndGcd(4);
  expect a == 1 && b == 3, "impl test: x=4";

  a, b := EhAbAndGcd(5);
  expect a == 1 && b == 4, "impl test: x=5";

  a, b := EhAbAndGcd(7);
  expect a == 1 && b == 6, "impl test: x=7";

  a, b := EhAbAndGcd(10);
  expect a == 1 && b == 9, "impl test: x=10";

  a, b := EhAbAndGcd(14);
  expect a == 1 && b == 13, "impl test: x=14";

  a, b := EhAbAndGcd(25);
  expect a == 1 && b == 24, "impl test: x=25";

  a, b := EhAbAndGcd(50);
  expect a == 1 && b == 49, "impl test: x=50";

  // Bulk implementation tests covering all provided inputs
  var inputs: seq<int> := [
    2, 14, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20,
    21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36,
    37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52,
    53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68,
    69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84,
    85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100,
    101, 102, 103
  ];

  var i := 0;
  while i < |inputs|
  {
    a, b := EhAbAndGcd(inputs[i]);
    expect a == 1, "impl bulk: wrong a";
    expect b == inputs[i] - 1, "impl bulk: wrong b";
    i := i + 1;
  }

  print "All tests passed\n";
}