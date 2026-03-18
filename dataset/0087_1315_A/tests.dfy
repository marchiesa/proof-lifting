predicate IsValidWindow(a: int, b: int, c1: int, r1: int, c2: int, r2: int)
{
  0 <= c1 <= c2 < a && 0 <= r1 <= r2 < b
}

predicate WindowAvoidsDead(c1: int, r1: int, c2: int, r2: int, x: int, y: int)
{
  x < c1 || x > c2 || y < r1 || y > r2
}

function WindowArea(c1: int, r1: int, c2: int, r2: int): int
{
  (c2 - c1 + 1) * (r2 - r1 + 1)
}

predicate DeadPixelSpec(a: int, b: int, x: int, y: int, area: int)
  requires a >= 1 && b >= 1
  requires 0 <= x < a && 0 <= y < b
{
  area >= 0 &&
  (forall c1, r1, c2, r2 | 0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b ::
    (IsValidWindow(a, b, c1, r1, c2, r2) && WindowAvoidsDead(c1, r1, c2, r2, x, y))
      ==> WindowArea(c1, r1, c2, r2) <= area) &&
  (area == 0 ||
    (exists c1, r1, c2, r2 | 0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b ::
      IsValidWindow(a, b, c1, r1, c2, r2) && WindowAvoidsDead(c1, r1, c2, r2, x, y) &&
      WindowArea(c1, r1, c2, r2) == area))
}

method DeadPixel(a: int, b: int, x: int, y: int) returns (area: int)
  requires a >= 1 && b >= 1
  requires 0 <= x < a && 0 <= y < b
  ensures area >= 0
  ensures forall c1, r1, c2, r2 | 0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b ::
    (IsValidWindow(a, b, c1, r1, c2, r2) && WindowAvoidsDead(c1, r1, c2, r2, x, y))
      ==> WindowArea(c1, r1, c2, r2) <= area
  ensures area == 0 ||
    (exists c1, r1, c2, r2 | 0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b ::
      IsValidWindow(a, b, c1, r1, c2, r2) && WindowAvoidsDead(c1, r1, c2, r2, x, y) &&
      WindowArea(c1, r1, c2, r2) == area)
{
  var v1 := x * b;
  var v2 := y * a;
  var v3 := (a - x - 1) * b;
  var v4 := (b - y - 1) * a;
  area := v1;
  if v2 > area { area := v2; }
  if v3 > area { area := v3; }
  if v4 > area { area := v4; }
  return;
}

method Main()
{
  var result: int;

  // ========== SPEC POSITIVE TESTS ==========
  // Using small inputs where bounded quantifier enumeration is feasible
  expect DeadPixelSpec(2, 1, 0, 0, 1), "spec positive 1";    // from test 1.4
  expect DeadPixelSpec(1, 2, 0, 0, 1), "spec positive 2";    // from test 3.1
  expect DeadPixelSpec(3, 3, 1, 1, 3), "spec positive 3";    // from test 4.1
  expect DeadPixelSpec(4, 4, 0, 0, 12), "spec positive 4";   // from test 4.2
  expect DeadPixelSpec(2, 2, 0, 0, 2), "spec positive 5";    // from test 6.1
  expect DeadPixelSpec(2, 2, 1, 1, 2), "spec positive 6";    // from test 6.2
  expect DeadPixelSpec(2, 2, 0, 1, 2), "spec positive 7";    // from test 6.3
  expect DeadPixelSpec(2, 2, 1, 0, 2), "spec positive 8";    // from test 6.4
  expect DeadPixelSpec(5, 5, 2, 2, 10), "spec positive 9";   // from test 9.2

  // ========== SPEC NEGATIVE TESTS ==========
  // Using small inputs with wrong (inflated) outputs — spec should reject
  expect !DeadPixelSpec(1, 2, 0, 0, 2), "spec negative 3";   // Neg 3: correct=1, wrong=2
  expect !DeadPixelSpec(3, 3, 1, 1, 4), "spec negative 4";   // Neg 4: correct=3, wrong=4
  expect !DeadPixelSpec(2, 2, 0, 0, 3), "spec negative 6";   // Neg 6: correct=2, wrong=3
  expect !DeadPixelSpec(7, 3, 3, 1, 10), "spec negative 9";  // Neg 9: correct=9, wrong=10
  expect !DeadPixelSpec(3, 7, 1, 3, 10), "spec negative 10"; // Neg 10: correct=9, wrong=10

  // ========== IMPLEMENTATION TESTS ==========
  // Test 1
  result := DeadPixel(8, 8, 0, 0);
  expect result == 56, "impl test 1.1 failed";
  result := DeadPixel(1, 10, 0, 3);
  expect result == 6, "impl test 1.2 failed";
  result := DeadPixel(17, 31, 10, 4);
  expect result == 442, "impl test 1.3 failed";
  result := DeadPixel(2, 1, 0, 0);
  expect result == 1, "impl test 1.4 failed";
  result := DeadPixel(5, 10, 3, 9);
  expect result == 45, "impl test 1.5 failed";
  result := DeadPixel(10, 10, 4, 8);
  expect result == 80, "impl test 1.6 failed";

  // Test 2
  result := DeadPixel(10, 10, 5, 5);
  expect result == 50, "impl test 2.1 failed";
  result := DeadPixel(1, 2, 0, 0);
  expect result == 1, "impl test 2.2 failed";
  result := DeadPixel(50, 50, 25, 25);
  expect result == 1250, "impl test 2.3 failed";

  // Test 3
  result := DeadPixel(1, 2, 0, 0);
  expect result == 1, "impl test 3.1 failed";

  // Test 4
  result := DeadPixel(3, 3, 1, 1);
  expect result == 3, "impl test 4.1 failed";
  result := DeadPixel(4, 4, 0, 0);
  expect result == 12, "impl test 4.2 failed";

  // Test 5
  result := DeadPixel(50, 50, 49, 49);
  expect result == 2450, "impl test 5.1 failed";

  // Test 6
  result := DeadPixel(2, 2, 0, 0);
  expect result == 2, "impl test 6.1 failed";
  result := DeadPixel(2, 2, 1, 1);
  expect result == 2, "impl test 6.2 failed";
  result := DeadPixel(2, 2, 0, 1);
  expect result == 2, "impl test 6.3 failed";
  result := DeadPixel(2, 2, 1, 0);
  expect result == 2, "impl test 6.4 failed";

  // Test 7
  result := DeadPixel(1, 50, 0, 25);
  expect result == 25, "impl test 7.1 failed";

  // Test 8
  result := DeadPixel(50, 1, 25, 0);
  expect result == 25, "impl test 8.1 failed";
  result := DeadPixel(10, 10, 0, 9);
  expect result == 90, "impl test 8.2 failed";
  result := DeadPixel(10, 10, 9, 0);
  expect result == 90, "impl test 8.3 failed";

  // Test 9
  result := DeadPixel(7, 3, 3, 1);
  expect result == 9, "impl test 9.1 failed";
  result := DeadPixel(5, 5, 2, 2);
  expect result == 10, "impl test 9.2 failed";

  // Test 10
  result := DeadPixel(3, 7, 1, 3);
  expect result == 9, "impl test 10.1 failed";
  result := DeadPixel(6, 4, 5, 3);
  expect result == 20, "impl test 10.2 failed";
  result := DeadPixel(8, 2, 7, 1);
  expect result == 14, "impl test 10.3 failed";
  result := DeadPixel(4, 9, 0, 4);
  expect result == 27, "impl test 10.4 failed";
  result := DeadPixel(9, 3, 4, 0);
  expect result == 18, "impl test 10.5 failed";

  // Test 11
  result := DeadPixel(10, 10, 5, 0);
  expect result == 90, "impl test 11.1 failed";

  print "All tests passed\n";
}