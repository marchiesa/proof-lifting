function ByColumnsNumber(n: int, row: int, col: int): int
{
  col * n + row + 1
}

function ByRowsNumber(m: int, row: int, col: int): int
{
  row * m + col + 1
}

predicate StrangeTableSpec(n: int, m: int, x: int, result: int)
{
  exists row | 0 <= row < n :: exists col | 0 <= col < m ::
    ByColumnsNumber(n, row, col) == x &&
    result == ByRowsNumber(m, row, col)
}

method StrangeTable(n: int, m: int, x: int) returns (result: int)
  requires n >= 1 && m >= 1
  requires 1 <= x <= n * m
  ensures StrangeTableSpec(n, m, x, result)
{
  var x0 := x - 1;
  var r := x0 / n;
  var c := x0 % n;
  result := c * m + r + 1;
}

method Main()
{
  var r: int;

  // ========== SPEC POSITIVE TESTS ==========
  // Using small inputs (n*m <= 100) for bounded quantifier evaluation.
  // Skipping (100,100,...) and (1000000,1000000,...) from Test 1.

  // Test 1 (small cases)
  expect StrangeTableSpec(1, 1, 1, 1), "spec positive 1.1";
  expect StrangeTableSpec(2, 2, 3, 2), "spec positive 1.2";
  expect StrangeTableSpec(3, 5, 11, 9), "spec positive 1.3";

  // Test 2
  expect StrangeTableSpec(1, 1, 1, 1), "spec positive 2.1";
  expect StrangeTableSpec(2, 3, 5, 3), "spec positive 2.2";
  expect StrangeTableSpec(4, 4, 16, 16), "spec positive 2.3";

  // Test 3
  expect StrangeTableSpec(3, 5, 11, 9), "spec positive 3.1";

  // Test 4
  expect StrangeTableSpec(5, 5, 25, 25), "spec positive 4.1";
  expect StrangeTableSpec(5, 5, 1, 1), "spec positive 4.2";

  // Test 5
  expect StrangeTableSpec(1, 10, 7, 7), "spec positive 5.1";
  expect StrangeTableSpec(10, 1, 7, 7), "spec positive 5.2";
  expect StrangeTableSpec(3, 3, 9, 9), "spec positive 5.3";
  expect StrangeTableSpec(2, 5, 10, 10), "spec positive 5.4";

  // Test 6
  expect StrangeTableSpec(7, 7, 49, 49), "spec positive 6.1";

  // Test 7
  expect StrangeTableSpec(2, 2, 1, 1), "spec positive 7.1";
  expect StrangeTableSpec(2, 2, 2, 3), "spec positive 7.2";
  expect StrangeTableSpec(2, 2, 4, 4), "spec positive 7.3";

  // Test 8
  expect StrangeTableSpec(1, 1, 1, 1), "spec positive 8.1";
  expect StrangeTableSpec(1, 5, 3, 3), "spec positive 8.2";
  expect StrangeTableSpec(5, 1, 3, 3), "spec positive 8.3";
  expect StrangeTableSpec(3, 3, 5, 5), "spec positive 8.4";
  expect StrangeTableSpec(4, 2, 7, 6), "spec positive 8.5";

  // Test 9
  expect StrangeTableSpec(6, 8, 48, 48), "spec positive 9.1";
  expect StrangeTableSpec(8, 6, 48, 48), "spec positive 9.2";

  // Test 10
  expect StrangeTableSpec(10, 10, 1, 1), "spec positive 10.1";
  expect StrangeTableSpec(10, 10, 50, 95), "spec positive 10.2";
  expect StrangeTableSpec(10, 10, 100, 100), "spec positive 10.3";
  expect StrangeTableSpec(10, 10, 37, 64), "spec positive 10.4";

  // ========== SPEC NEGATIVE TESTS ==========
  // Testing that the spec rejects wrong outputs.

  // Negative 1: (1,1,1) correct=1, wrong=2
  expect !StrangeTableSpec(1, 1, 1, 2), "spec negative 1";

  // Negative 2: (1,1,1) correct=1, wrong=2
  expect !StrangeTableSpec(1, 1, 1, 2), "spec negative 2";

  // Negative 3: (3,5,11) correct=9, wrong=10
  expect !StrangeTableSpec(3, 5, 11, 10), "spec negative 3";

  // Negative 4: (5,5,25) correct=25, wrong=26
  expect !StrangeTableSpec(5, 5, 25, 26), "spec negative 4";

  // Negative 5: (1,10,7) correct=7, wrong=8
  expect !StrangeTableSpec(1, 10, 7, 8), "spec negative 5";

  // Negative 6: (7,7,49) correct=49, wrong=50
  expect !StrangeTableSpec(7, 7, 49, 50), "spec negative 6";

  // Negative 7: (2,2,1) correct=1, wrong=2
  expect !StrangeTableSpec(2, 2, 1, 2), "spec negative 7";

  // Negative 8: (1,1,1) correct=1, wrong=2
  expect !StrangeTableSpec(1, 1, 1, 2), "spec negative 8";

  // Negative 9: (6,8,48) correct=48, wrong=49
  expect !StrangeTableSpec(6, 8, 48, 49), "spec negative 9";

  // Negative 10: (10,10,1) correct=1, wrong=2
  expect !StrangeTableSpec(10, 10, 1, 2), "spec negative 10";

  // ========== IMPLEMENTATION TESTS ==========

  // Test 1
  r := StrangeTable(1, 1, 1);
  expect r == 1, "impl test 1.1 failed";
  r := StrangeTable(2, 2, 3);
  expect r == 2, "impl test 1.2 failed";
  r := StrangeTable(3, 5, 11);
  expect r == 9, "impl test 1.3 failed";
  r := StrangeTable(100, 100, 7312);
  expect r == 1174, "impl test 1.4 failed";
  r := StrangeTable(1000000, 1000000, 1000000000000);
  expect r == 1000000000000, "impl test 1.5 failed";

  // Test 2
  r := StrangeTable(1, 1, 1);
  expect r == 1, "impl test 2.1 failed";
  r := StrangeTable(2, 3, 5);
  expect r == 3, "impl test 2.2 failed";
  r := StrangeTable(4, 4, 16);
  expect r == 16, "impl test 2.3 failed";

  // Test 3
  r := StrangeTable(3, 5, 11);
  expect r == 9, "impl test 3.1 failed";

  // Test 4
  r := StrangeTable(5, 5, 25);
  expect r == 25, "impl test 4.1 failed";
  r := StrangeTable(5, 5, 1);
  expect r == 1, "impl test 4.2 failed";

  // Test 5
  r := StrangeTable(1, 10, 7);
  expect r == 7, "impl test 5.1 failed";
  r := StrangeTable(10, 1, 7);
  expect r == 7, "impl test 5.2 failed";
  r := StrangeTable(3, 3, 9);
  expect r == 9, "impl test 5.3 failed";
  r := StrangeTable(2, 5, 10);
  expect r == 10, "impl test 5.4 failed";

  // Test 6
  r := StrangeTable(7, 7, 49);
  expect r == 49, "impl test 6.1 failed";

  // Test 7
  r := StrangeTable(2, 2, 1);
  expect r == 1, "impl test 7.1 failed";
  r := StrangeTable(2, 2, 2);
  expect r == 3, "impl test 7.2 failed";
  r := StrangeTable(2, 2, 4);
  expect r == 4, "impl test 7.3 failed";

  // Test 8
  r := StrangeTable(1, 1, 1);
  expect r == 1, "impl test 8.1 failed";
  r := StrangeTable(1, 5, 3);
  expect r == 3, "impl test 8.2 failed";
  r := StrangeTable(5, 1, 3);
  expect r == 3, "impl test 8.3 failed";
  r := StrangeTable(3, 3, 5);
  expect r == 5, "impl test 8.4 failed";
  r := StrangeTable(4, 2, 7);
  expect r == 6, "impl test 8.5 failed";

  // Test 9
  r := StrangeTable(6, 8, 48);
  expect r == 48, "impl test 9.1 failed";
  r := StrangeTable(8, 6, 48);
  expect r == 48, "impl test 9.2 failed";

  // Test 10
  r := StrangeTable(10, 10, 1);
  expect r == 1, "impl test 10.1 failed";
  r := StrangeTable(10, 10, 50);
  expect r == 95, "impl test 10.2 failed";
  r := StrangeTable(10, 10, 100);
  expect r == 100, "impl test 10.3 failed";
  r := StrangeTable(10, 10, 37);
  expect r == 64, "impl test 10.4 failed";

  // Test 11
  r := StrangeTable(3, 4, 12);
  expect r == 12, "impl test 11.1 failed";
  r := StrangeTable(4, 3, 12);
  expect r == 12, "impl test 11.2 failed";
  r := StrangeTable(2, 7, 14);
  expect r == 14, "impl test 11.3 failed";

  print "All tests passed\n";
}