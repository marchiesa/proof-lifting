predicate ValidAssignment(x: int, y: int, a: int, b: int, c: int, d: int, k: int)
{
  x >= 0 && y >= 0 && x * c >= a && y * d >= b && x + y <= k
}

predicate Feasible(a: int, b: int, c: int, d: int, k: int)
{
  exists x | 0 <= x <= k :: exists y | 0 <= y <= k :: ValidAssignment(x, y, a, b, c, d, k)
}

predicate Postcondition(x: int, y: int, a: int, b: int, c: int, d: int, k: int)
{
  (Feasible(a, b, c, d, k) ==> ValidAssignment(x, y, a, b, c, d, k)) &&
  (!Feasible(a, b, c, d, k) ==> x == -1)
}

method PensAndPencils(a: int, b: int, c: int, d: int, k: int) returns (x: int, y: int)
  requires a >= 1 && b >= 1 && c >= 1 && d >= 1 && k >= 1
  ensures Feasible(a, b, c, d, k) ==> ValidAssignment(x, y, a, b, c, d, k)
  ensures !Feasible(a, b, c, d, k) ==> x == -1
{
  var pens := (a + c - 1) / c;
  var pencils := (b + d - 1) / d;
  if pens + pencils <= k {
    return pens, pencils;
  } else {
    return -1, 0;
  }
}

method Main()
{
  var x: int, y: int;

  // === SPEC POSITIVE TESTS ===
  // Using small k values so bounded quantifiers in Feasible are fast

  // From Test 5: (2,2,2,3,2) -> (1,1) feasible
  expect Postcondition(1, 1, 2, 2, 2, 3, 2), "spec positive 1";

  // From Test 7: (1,1,6,7,2) -> (1,1) feasible
  expect Postcondition(1, 1, 1, 1, 6, 7, 2), "spec positive 2";

  // From Test 8: (1,1,1,7,2) -> (1,1) feasible
  expect Postcondition(1, 1, 1, 1, 1, 7, 2), "spec positive 3";

  // From Test 9: (1,2,5,2,2) -> (1,1) feasible
  expect Postcondition(1, 1, 1, 2, 5, 2, 2), "spec positive 4";

  // From Test 3: (2,5,4,2,2) -> -1 infeasible
  expect Postcondition(-1, 0, 2, 5, 4, 2, 2), "spec positive 5";

  // From Test 6: (1,6,3,2,3) -> -1 infeasible
  expect Postcondition(-1, 0, 1, 6, 3, 2, 3), "spec positive 6";

  // From Test 20: (1,1,1,1,2) -> (1,1) feasible
  expect Postcondition(1, 1, 1, 1, 1, 1, 2), "spec positive 7";

  // From Test 16: (4,1,7,1,2) -> (1,1) feasible
  expect Postcondition(1, 1, 4, 1, 7, 1, 2), "spec positive 8";

  // From Test 17: (1,1,1,6,2) -> (1,1) feasible
  expect Postcondition(1, 1, 1, 1, 1, 6, 2), "spec positive 9";

  // From Test 18: (2,1,3,8,2) -> (1,1) feasible
  expect Postcondition(1, 1, 2, 1, 3, 8, 2), "spec positive 10";

  // From Test 4: (5,4,6,1,5) -> (1,4) feasible
  expect Postcondition(1, 4, 5, 4, 6, 1, 5), "spec positive 11";

  // === SPEC NEGATIVE TESTS ===
  // Wrong outputs that violate the postcondition

  // Neg 5: (2,2,2,3,2) wrong=(2,1) — x+y=3 > k=2, VA fails
  expect !Postcondition(2, 1, 2, 2, 2, 3, 2), "spec negative 1";

  // Neg 7: (1,1,6,7,2) wrong=(2,1) — x+y=3 > k=2, VA fails
  expect !Postcondition(2, 1, 1, 1, 6, 7, 2), "spec negative 2";

  // Neg 8: (1,1,1,7,2) wrong=(2,1) — x+y=3 > k=2, VA fails
  expect !Postcondition(2, 1, 1, 1, 1, 7, 2), "spec negative 3";

  // Neg 9: (1,2,5,2,2) wrong=(2,1) — x+y=3 > k=2, VA fails
  expect !Postcondition(2, 1, 1, 2, 5, 2, 2), "spec negative 4";

  // Neg 3: (2,5,4,2,2) wrong x=0 instead of -1 — infeasible but x != -1
  expect !Postcondition(0, 0, 2, 5, 4, 2, 2), "spec negative 5";

  // Neg 6: (1,6,3,2,3) wrong x=0 instead of -1 — infeasible but x != -1
  expect !Postcondition(0, 0, 1, 6, 3, 2, 3), "spec negative 6";

  // Neg 4: (5,4,6,1,5) wrong=(2,4) — x+y=6 > k=5, VA fails
  expect !Postcondition(2, 4, 5, 4, 6, 1, 5), "spec negative 7";

  // === IMPLEMENTATION TESTS ===

  // Test 1.1
  x, y := PensAndPencils(7, 5, 4, 5, 8);
  expect x == 2 && y == 1, "impl test 1.1 failed";

  // Test 1.2
  x, y := PensAndPencils(7, 5, 4, 5, 2);
  expect x == -1, "impl test 1.2 failed";

  // Test 1.3
  x, y := PensAndPencils(20, 53, 45, 26, 4);
  expect x == 1 && y == 3, "impl test 1.3 failed";

  // Test 2.1
  x, y := PensAndPencils(80, 72, 20, 12, 10);
  expect x == 4 && y == 6, "impl test 2.1 failed";

  // Test 2.2
  x, y := PensAndPencils(81, 72, 20, 12, 11);
  expect x == 5 && y == 6, "impl test 2.2 failed";

  // Test 2.3
  x, y := PensAndPencils(80, 73, 20, 12, 11);
  expect x == 4 && y == 7, "impl test 2.3 failed";

  // Test 2.4
  x, y := PensAndPencils(81, 73, 20, 12, 12);
  expect x == 5 && y == 7, "impl test 2.4 failed";

  // Test 2.5
  x, y := PensAndPencils(80, 73, 20, 12, 10);
  expect x == -1, "impl test 2.5 failed";

  // Test 2.6
  x, y := PensAndPencils(3, 99, 5, 1, 100);
  expect x == 1 && y == 99, "impl test 2.6 failed";

  // Test 2.7
  x, y := PensAndPencils(99, 1, 1, 4, 100);
  expect x == 99 && y == 1, "impl test 2.7 failed";

  // Test 2.8
  x, y := PensAndPencils(53, 37, 13, 3, 17);
  expect x == -1, "impl test 2.8 failed";

  // Test 3
  x, y := PensAndPencils(2, 5, 4, 2, 2);
  expect x == -1, "impl test 3 failed";

  // Test 4
  x, y := PensAndPencils(5, 4, 6, 1, 5);
  expect x == 1 && y == 4, "impl test 4 failed";

  // Test 5
  x, y := PensAndPencils(2, 2, 2, 3, 2);
  expect x == 1 && y == 1, "impl test 5 failed";

  // Test 6
  x, y := PensAndPencils(1, 6, 3, 2, 3);
  expect x == -1, "impl test 6 failed";

  // Test 7
  x, y := PensAndPencils(1, 1, 6, 7, 2);
  expect x == 1 && y == 1, "impl test 7 failed";

  // Test 8
  x, y := PensAndPencils(1, 1, 1, 7, 2);
  expect x == 1 && y == 1, "impl test 8 failed";

  // Test 9
  x, y := PensAndPencils(1, 2, 5, 2, 2);
  expect x == 1 && y == 1, "impl test 9 failed";

  // Test 10
  x, y := PensAndPencils(3, 99, 5, 1, 100);
  expect x == 1 && y == 99, "impl test 10 failed";

  // Test 11
  x, y := PensAndPencils(7, 4, 5, 1, 5);
  expect x == -1, "impl test 11 failed";

  // Test 12
  x, y := PensAndPencils(99, 1, 1, 4, 100);
  expect x == 99 && y == 1, "impl test 12 failed";

  // Test 13
  x, y := PensAndPencils(99, 6, 1, 8, 100);
  expect x == 99 && y == 1, "impl test 13 failed";

  // Test 14
  x, y := PensAndPencils(7, 2, 3, 2, 3);
  expect x == -1, "impl test 14 failed";

  // Test 15
  x, y := PensAndPencils(3, 99, 6, 1, 100);
  expect x == 1 && y == 99, "impl test 15 failed";

  // Test 16
  x, y := PensAndPencils(4, 1, 7, 1, 2);
  expect x == 1 && y == 1, "impl test 16 failed";

  // Test 17
  x, y := PensAndPencils(1, 1, 1, 6, 2);
  expect x == 1 && y == 1, "impl test 17 failed";

  // Test 18
  x, y := PensAndPencils(2, 1, 3, 8, 2);
  expect x == 1 && y == 1, "impl test 18 failed";

  // Test 19
  x, y := PensAndPencils(3, 1, 3, 1, 7);
  expect x == 1 && y == 1, "impl test 19 failed";

  // Test 20
  x, y := PensAndPencils(1, 1, 1, 1, 2);
  expect x == 1 && y == 1, "impl test 20 failed";

  print "All tests passed\n";
}