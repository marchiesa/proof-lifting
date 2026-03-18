function MaxOf(a: int, b: int): int {
  if a > b then a else b
}

function MinOf(a: int, b: int): int {
  if a < b then a else b
}

predicate IsValidSolution(x: int, y: int, z: int, a: int, b: int, c: int) {
  a > 0 && b > 0 && c > 0 &&
  MaxOf(a, b) == x && MaxOf(a, c) == y && MaxOf(b, c) == z
}

predicate SolutionExists(x: int, y: int, z: int)
  requires x > 0 && y > 0 && z > 0
{
  exists a | 1 <= a <= MinOf(x, y) ::
    exists b | 1 <= b <= MinOf(x, z) ::
      exists c | 1 <= c <= MinOf(y, z) ::
        IsValidSolution(x, y, z, a, b, c)
}

method ThreePairwiseMaximums(x: int, y: int, z: int) returns (possible: bool, a: int, b: int, c: int)
  requires x > 0 && y > 0 && z > 0
  ensures possible == SolutionExists(x, y, z)
  ensures possible ==> IsValidSolution(x, y, z, a, b, c)
{
  var m := x;
  if y > m { m := y; }
  if z > m { m := z; }

  var cnt := 0;
  if x == m { cnt := cnt + 1; }
  if y == m { cnt := cnt + 1; }
  if z == m { cnt := cnt + 1; }

  if cnt >= 2 {
    possible := true;
    a := if x <= y then x else y;
    b := if x <= z then x else z;
    c := if y <= z then y else z;
  } else {
    possible := false;
    a := 0;
    b := 0;
    c := 0;
  }
}

method Main()
{
  var p: bool;
  var a: int;
  var b: int;
  var c: int;

  // ===== SPEC POSITIVE TESTS =====
  // Top-level ensures: possible == SolutionExists(x,y,z)
  //                    possible ==> IsValidSolution(x,y,z,a,b,c)
  // Small inputs only for SolutionExists (bounded quantifier enumeration).

  // Spec positive 1: from Test 1.1 (3,2,3) -> YES, (2,3,2)
  expect SolutionExists(3, 2, 3), "spec positive 1a";
  expect IsValidSolution(3, 2, 3, 2, 3, 2), "spec positive 1b";

  // Spec positive 2: from Test 1.2 (100,100,100) scaled to (2,2,2) -> YES, (2,2,2)
  expect SolutionExists(2, 2, 2), "spec positive 2a";
  expect IsValidSolution(2, 2, 2, 2, 2, 2), "spec positive 2b";

  // Spec positive 3: from Test 1.3 (50,49,49) scaled to (3,2,2) -> NO
  expect !SolutionExists(3, 2, 2), "spec positive 3";

  // Spec positive 4: from Test 1.4 (10,30,20) scaled to (1,3,2) -> NO
  expect !SolutionExists(1, 3, 2), "spec positive 4";

  // Spec positive 5: from Test 1.5 (1,1e9,1e9) scaled to (1,2,2) -> YES, (1,1,2)
  expect SolutionExists(1, 2, 2), "spec positive 5a";
  expect IsValidSolution(1, 2, 2, 1, 1, 2), "spec positive 5b";

  // Spec positive 6: from Test 2.1 (5,7,7) scaled to (2,3,3) -> YES, (2,2,3)
  expect SolutionExists(2, 3, 3), "spec positive 6a";
  expect IsValidSolution(2, 3, 3, 2, 2, 3), "spec positive 6b";

  // Spec positive 7: from Test 2.2 (6,7,3) scaled to (2,3,1) -> NO
  expect !SolutionExists(2, 3, 1), "spec positive 7";

  // Spec positive 8: from Test 3 (127869^3) scaled to (3,3,3) -> YES, (3,3,3)
  expect SolutionExists(3, 3, 3), "spec positive 8a";
  expect IsValidSolution(3, 3, 3, 3, 3, 3), "spec positive 8b";

  // Spec positive 9: from Test 4 (12789^3) scaled to (1,1,1) -> YES, (1,1,1)
  expect SolutionExists(1, 1, 1), "spec positive 9a";
  expect IsValidSolution(1, 1, 1, 1, 1, 1), "spec positive 9b";

  // Spec positive 10: from Test 5 (78738^3) scaled to (4,4,4) -> YES, (4,4,4)
  expect SolutionExists(4, 4, 4), "spec positive 10a";
  expect IsValidSolution(4, 4, 4, 4, 4, 4), "spec positive 10b";

  // Spec positive 11: from Test 6 (78788^3) scaled to (5,5,5) -> YES, (5,5,5)
  expect SolutionExists(5, 5, 5), "spec positive 11a";
  expect IsValidSolution(5, 5, 5, 5, 5, 5), "spec positive 11b";

  // ===== SPEC NEGATIVE TESTS =====
  // Wrong outputs must be rejected by the top-level ensures predicates.
  // Each maps to a negative test pair with perturbed (a,b,c) values.

  // Spec negative 1: from Neg 1 — (1,2,2) wrong (1,1,3) instead of correct (1,1,2)
  expect !IsValidSolution(1, 2, 2, 1, 1, 3), "spec negative 1";

  // Spec negative 2: from Neg 2 — (2,3,1) NO case, bogus claim (1,1,1) is invalid
  expect !IsValidSolution(2, 3, 1, 1, 1, 1), "spec negative 2";

  // Spec negative 3: from Neg 3 — (3,3,3) wrong (3,3,4) instead of correct (3,3,3)
  expect !IsValidSolution(3, 3, 3, 3, 3, 4), "spec negative 3";

  // Spec negative 4: from Neg 4 — (1,1,1) wrong (1,1,2) instead of correct (1,1,1)
  expect !IsValidSolution(1, 1, 1, 1, 1, 2), "spec negative 4";

  // Spec negative 5: from Neg 5 — (4,4,4) wrong (4,4,5) instead of correct (4,4,4)
  expect !IsValidSolution(4, 4, 4, 4, 4, 5), "spec negative 5";

  // Spec negative 6: from Neg 6 — (5,5,5) wrong (5,5,6) instead of correct (5,5,5)
  expect !IsValidSolution(5, 5, 5, 5, 5, 6), "spec negative 6";

  // ===== IMPLEMENTATION TESTS =====

  // Impl 1.1: (3, 2, 3) -> YES
  p, a, b, c := ThreePairwiseMaximums(3, 2, 3);
  expect p == true, "impl 1.1: expected possible";
  expect a > 0 && b > 0 && c > 0, "impl 1.1: positive";
  expect MaxOf(a, b) == 3, "impl 1.1: max(a,b)";
  expect MaxOf(a, c) == 2, "impl 1.1: max(a,c)";
  expect MaxOf(b, c) == 3, "impl 1.1: max(b,c)";

  // Impl 1.2: (100, 100, 100) -> YES
  p, a, b, c := ThreePairwiseMaximums(100, 100, 100);
  expect p == true, "impl 1.2: expected possible";
  expect a > 0 && b > 0 && c > 0, "impl 1.2: positive";
  expect MaxOf(a, b) == 100, "impl 1.2: max(a,b)";
  expect MaxOf(a, c) == 100, "impl 1.2: max(a,c)";
  expect MaxOf(b, c) == 100, "impl 1.2: max(b,c)";

  // Impl 1.3: (50, 49, 49) -> NO
  p, a, b, c := ThreePairwiseMaximums(50, 49, 49);
  expect p == false, "impl 1.3: expected not possible";

  // Impl 1.4: (10, 30, 20) -> NO
  p, a, b, c := ThreePairwiseMaximums(10, 30, 20);
  expect p == false, "impl 1.4: expected not possible";

  // Impl 1.5: (1, 1000000000, 1000000000) -> YES
  p, a, b, c := ThreePairwiseMaximums(1, 1000000000, 1000000000);
  expect p == true, "impl 1.5: expected possible";
  expect a > 0 && b > 0 && c > 0, "impl 1.5: positive";
  expect MaxOf(a, b) == 1, "impl 1.5: max(a,b)";
  expect MaxOf(a, c) == 1000000000, "impl 1.5: max(a,c)";
  expect MaxOf(b, c) == 1000000000, "impl 1.5: max(b,c)";

  // Impl 2.1: (5, 7, 7) -> YES
  p, a, b, c := ThreePairwiseMaximums(5, 7, 7);
  expect p == true, "impl 2.1: expected possible";
  expect a > 0 && b > 0 && c > 0, "impl 2.1: positive";
  expect MaxOf(a, b) == 5, "impl 2.1: max(a,b)";
  expect MaxOf(a, c) == 7, "impl 2.1: max(a,c)";
  expect MaxOf(b, c) == 7, "impl 2.1: max(b,c)";

  // Impl 2.2: (6, 7, 3) -> NO
  p, a, b, c := ThreePairwiseMaximums(6, 7, 3);
  expect p == false, "impl 2.2: expected not possible";

  // Impl 3: (127869, 127869, 127869) -> YES
  p, a, b, c := ThreePairwiseMaximums(127869, 127869, 127869);
  expect p == true, "impl 3: expected possible";
  expect a > 0 && b > 0 && c > 0, "impl 3: positive";
  expect MaxOf(a, b) == 127869, "impl 3: max(a,b)";
  expect MaxOf(a, c) == 127869, "impl 3: max(a,c)";
  expect MaxOf(b, c) == 127869, "impl 3: max(b,c)";

  // Impl 4: (12789, 12789, 12789) -> YES
  p, a, b, c := ThreePairwiseMaximums(12789, 12789, 12789);
  expect p == true, "impl 4: expected possible";
  expect a > 0 && b > 0 && c > 0, "impl 4: positive";
  expect MaxOf(a, b) == 12789, "impl 4: max(a,b)";
  expect MaxOf(a, c) == 12789, "impl 4: max(a,c)";
  expect MaxOf(b, c) == 12789, "impl 4: max(b,c)";

  // Impl 5: (78738, 78738, 78738) -> YES
  p, a, b, c := ThreePairwiseMaximums(78738, 78738, 78738);
  expect p == true, "impl 5: expected possible";
  expect a > 0 && b > 0 && c > 0, "impl 5: positive";
  expect MaxOf(a, b) == 78738, "impl 5: max(a,b)";
  expect MaxOf(a, c) == 78738, "impl 5: max(a,c)";
  expect MaxOf(b, c) == 78738, "impl 5: max(b,c)";

  // Impl 6: (78788, 78788, 78788) -> YES
  p, a, b, c := ThreePairwiseMaximums(78788, 78788, 78788);
  expect p == true, "impl 6: expected possible";
  expect a > 0 && b > 0 && c > 0, "impl 6: positive";
  expect MaxOf(a, b) == 78788, "impl 6: max(a,b)";
  expect MaxOf(a, c) == 78788, "impl 6: max(a,c)";
  expect MaxOf(b, c) == 78788, "impl 6: max(b,c)";

  print "All tests passed\n";
}