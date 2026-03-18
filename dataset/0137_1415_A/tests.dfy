predicate InGrid(n: int, m: int, i: int, j: int)
{
  1 <= i <= n && 1 <= j <= m
}

function ReachableWithin(n: int, m: int, ti: int, tj: int, t: int): set<(int, int)>
  requires n >= 1 && m >= 1
  requires InGrid(n, m, ti, tj)
  requires t >= 0
  decreases t
{
  if t == 0 then
    {(ti, tj)}
  else
    var prev := ReachableWithin(n, m, ti, tj, t - 1);
    set i: int, j: int | 1 <= i <= n && 1 <= j <= m &&
      ((i, j) in prev ||
       (i - 1 >= 1 && (i - 1, j) in prev) ||
       (i + 1 <= n && (i + 1, j) in prev) ||
       (j - 1 >= 1 && (i, j - 1) in prev) ||
       (j + 1 <= m && (i, j + 1) in prev))
    :: (i, j)
}

predicate AllReachWithin(n: int, m: int, ti: int, tj: int, t: int)
  requires n >= 1 && m >= 1
  requires InGrid(n, m, ti, tj)
  requires t >= 0
{
  var reach := ReachableWithin(n, m, ti, tj, t);
  forall i, j | 1 <= i <= n && 1 <= j <= m :: (i, j) in reach
}

predicate IsOptimalTime(n: int, m: int, r: int, c: int, time: int)
  requires n >= 1 && m >= 1
  requires InGrid(n, m, r, c)
  requires time >= 0
{
  AllReachWithin(n, m, r, c, time) &&
  (time == 0 || !AllReachWithin(n, m, r, c, time - 1))
}

method PrisonBreak(n: int, m: int, r: int, c: int) returns (time: int)
  requires n >= 1 && m >= 1
  requires InGrid(n, m, r, c)
  ensures time >= 0
  ensures AllReachWithin(n, m, r, c, time)
  ensures time == 0 || !AllReachWithin(n, m, r, c, time - 1)
{
  var dr: int;
  if r - 1 > n - r { dr := r - 1; } else { dr := n - r; }
  var dc: int;
  if c - 1 > m - c { dc := c - 1; } else { dc := m - c; }
  time := dr + dc;
}

method Main()
{
  var result: int;

  // ===== SPEC POSITIVE TESTS =====
  // Test IsOptimalTime with small inputs (from positive test pairs)

  // From Test 2: (1,1,1,1) -> 0
  expect IsOptimalTime(1, 1, 1, 1, 0), "spec positive 1";

  // From Test 8: (2,2,1,1) -> 2
  expect IsOptimalTime(2, 2, 1, 1, 2), "spec positive 2";

  // From Test 8: (3,3,2,2) -> 2
  expect IsOptimalTime(3, 3, 2, 2, 2), "spec positive 3";

  // From Test 8: (2,2,1,2) -> 2
  expect IsOptimalTime(2, 2, 1, 2, 2), "spec positive 4";

  // From Test 8: (2,2,2,1) -> 2
  expect IsOptimalTime(2, 2, 2, 1, 2), "spec positive 5";

  // From Test 8: (2,2,2,2) -> 2
  expect IsOptimalTime(2, 2, 2, 2, 2), "spec positive 6";

  // From Test 8: (3,3,1,1) -> 4
  expect IsOptimalTime(3, 3, 1, 1, 4), "spec positive 7";

  // From Test 10: (2,3,1,2) -> 2
  expect IsOptimalTime(2, 3, 1, 2, 2), "spec positive 8";

  // ===== SPEC NEGATIVE TESTS =====
  // Test that wrong outputs are rejected (scaled to small inputs)

  // Scaled from Neg 2: (1,1,1,1) wrong=1
  expect !IsOptimalTime(1, 1, 1, 1, 1), "spec negative 1";

  // Scaled from Neg 8: (2,2,1,1) wrong=3
  expect !IsOptimalTime(2, 2, 1, 1, 3), "spec negative 2";

  // Scaled from Neg 1: (3,3,1,1) wrong=5, correct=4
  expect !IsOptimalTime(3, 3, 1, 1, 5), "spec negative 3";

  // Scaled from Neg 3: (3,3,2,2) wrong=3, correct=2
  expect !IsOptimalTime(3, 3, 2, 2, 3), "spec negative 4";

  // Scaled from Neg 9: (2,2,2,2) wrong=3, correct=2
  expect !IsOptimalTime(2, 2, 2, 2, 3), "spec negative 5";

  // Scaled from Neg 6: (3,2,2,1) wrong=3, correct=2
  expect !IsOptimalTime(3, 2, 2, 1, 3), "spec negative 6";

  // Scaled from Neg 10: (2,3,1,2) wrong=3, correct=2
  expect !IsOptimalTime(2, 3, 1, 2, 3), "spec negative 7";

  // ===== IMPLEMENTATION TESTS =====

  // Test 1
  result := PrisonBreak(10, 10, 1, 1);
  expect result == 18, "impl test 1a failed";
  result := PrisonBreak(3, 5, 2, 4);
  expect result == 4, "impl test 1b failed";
  result := PrisonBreak(10, 2, 5, 1);
  expect result == 6, "impl test 1c failed";

  // Test 2
  result := PrisonBreak(1, 1, 1, 1);
  expect result == 0, "impl test 2 failed";

  // Test 3
  result := PrisonBreak(50, 50, 25, 25);
  expect result == 50, "impl test 3 failed";

  // Test 4
  result := PrisonBreak(1, 1, 1, 1);
  expect result == 0, "impl test 4a failed";
  result := PrisonBreak(2, 2, 1, 1);
  expect result == 2, "impl test 4b failed";
  result := PrisonBreak(3, 3, 2, 2);
  expect result == 2, "impl test 4c failed";
  result := PrisonBreak(4, 4, 1, 4);
  expect result == 6, "impl test 4d failed";
  result := PrisonBreak(5, 5, 5, 5);
  expect result == 8, "impl test 4e failed";

  // Test 5
  result := PrisonBreak(50, 50, 1, 1);
  expect result == 98, "impl test 5 failed";

  // Test 6
  result := PrisonBreak(7, 3, 4, 2);
  expect result == 4, "impl test 6a failed";
  result := PrisonBreak(1, 50, 1, 25);
  expect result == 25, "impl test 6b failed";
  result := PrisonBreak(50, 1, 25, 1);
  expect result == 25, "impl test 6c failed";
  result := PrisonBreak(6, 8, 6, 8);
  expect result == 12, "impl test 6d failed";

  // Test 7
  result := PrisonBreak(10, 10, 10, 10);
  expect result == 18, "impl test 7a failed";
  result := PrisonBreak(20, 30, 1, 30);
  expect result == 48, "impl test 7b failed";

  // Test 8
  result := PrisonBreak(2, 2, 1, 1);
  expect result == 2, "impl test 8a failed";
  result := PrisonBreak(2, 2, 1, 2);
  expect result == 2, "impl test 8b failed";
  result := PrisonBreak(2, 2, 2, 1);
  expect result == 2, "impl test 8c failed";
  result := PrisonBreak(2, 2, 2, 2);
  expect result == 2, "impl test 8d failed";
  result := PrisonBreak(3, 3, 1, 1);
  expect result == 4, "impl test 8e failed";
  result := PrisonBreak(3, 3, 2, 2);
  expect result == 2, "impl test 8f failed";

  // Test 9
  result := PrisonBreak(50, 50, 50, 50);
  expect result == 98, "impl test 9a failed";
  result := PrisonBreak(50, 50, 1, 50);
  expect result == 98, "impl test 9b failed";
  result := PrisonBreak(50, 50, 25, 1);
  expect result == 74, "impl test 9c failed";

  // Test 10
  result := PrisonBreak(1, 1, 1, 1);
  expect result == 0, "impl test 10a failed";
  result := PrisonBreak(5, 5, 3, 3);
  expect result == 4, "impl test 10b failed";
  result := PrisonBreak(4, 7, 2, 5);
  expect result == 6, "impl test 10c failed";
  result := PrisonBreak(8, 3, 1, 1);
  expect result == 9, "impl test 10d failed";
  result := PrisonBreak(6, 6, 6, 6);
  expect result == 10, "impl test 10e failed";
  result := PrisonBreak(10, 10, 5, 5);
  expect result == 10, "impl test 10f failed";
  result := PrisonBreak(3, 9, 2, 8);
  expect result == 8, "impl test 10g failed";
  result := PrisonBreak(7, 7, 4, 4);
  expect result == 6, "impl test 10h failed";
  result := PrisonBreak(2, 3, 1, 2);
  expect result == 2, "impl test 10i failed";
  result := PrisonBreak(15, 20, 8, 10);
  expect result == 17, "impl test 10j failed";

  print "All tests passed\n";
}