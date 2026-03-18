predicate Suffers(i: int, k: int, l: int, m: int, n: int)
  requires k > 0 && l > 0 && m > 0 && n > 0
{
  i % k == 0 || i % l == 0 || i % m == 0 || i % n == 0
}

function CountSuffered(k: int, l: int, m: int, n: int, d: int): int
  requires k > 0 && l > 0 && m > 0 && n > 0
  requires d >= 0
  decreases d
{
  if d == 0 then 0
  else CountSuffered(k, l, m, n, d - 1) + (if Suffers(d, k, l, m, n) then 1 else 0)
}

method InsomniaCure(k: int, l: int, m: int, n: int, d: int) returns (count: int)
  requires k > 0 && l > 0 && m > 0 && n > 0
  requires d >= 0
  ensures count == CountSuffered(k, l, m, n, d)
{
  count := 0;
  var i := 1;
  while i <= d
  {
    if i % k == 0 || i % l == 0 || i % m == 0 || i % n == 0 {
      count := count + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  var result: int;

  // ===== SPEC POSITIVE TESTS =====
  // Testing: count == CountSuffered(k, l, m, n, d)
  // Using small d values to keep recursive evaluation feasible.

  // Test 1: k=1,l=2,m=3,n=4,d=12 -> 12 (k=1 hits all)
  expect CountSuffered(1, 2, 3, 4, 12) == 12, "spec positive 1";

  // Test 2 (scaled): k=2,l=3,m=4,n=5,d=5 -> 4
  expect CountSuffered(2, 3, 4, 5, 5) == 4, "spec positive 2";

  // Test 3 (scaled): k=1,l=1,m=1,n=1,d=5 -> 5
  expect CountSuffered(1, 1, 1, 1, 5) == 5, "spec positive 3";

  // Test 4: k=10,l=9,m=8,n=7,d=6 -> 0
  expect CountSuffered(10, 9, 8, 7, 6) == 0, "spec positive 4";

  // Test 5 (scaled): k=8,l=4,m=4,n=3,d=12 -> 6
  expect CountSuffered(8, 4, 4, 3, 12) == 6, "spec positive 5";

  // Test 6 (scaled): k=8,l=4,m=1,n=10,d=5 -> 5 (m=1 hits all)
  expect CountSuffered(8, 4, 1, 10, 5) == 5, "spec positive 6";

  // Test 7 (scaled): k=4,l=1,m=8,n=7,d=5 -> 5 (l=1 hits all)
  expect CountSuffered(4, 1, 8, 7, 5) == 5, "spec positive 7";

  // Test 8 (scaled): k=6,l=1,m=7,n=2,d=5 -> 5 (l=1 hits all)
  expect CountSuffered(6, 1, 7, 2, 5) == 5, "spec positive 8";

  // Test 9 (scaled): k=2,l=7,m=4,n=9,d=10 -> 7
  expect CountSuffered(2, 7, 4, 9, 10) == 7, "spec positive 9";

  // Test 10 (scaled): k=2,l=9,m=8,n=1,d=5 -> 5 (n=1 hits all)
  expect CountSuffered(2, 9, 8, 1, 5) == 5, "spec positive 10";

  // ===== SPEC NEGATIVE TESTS =====
  // Same inputs, wrong outputs (off by +1, matching the negative test pattern).

  // Negative 1: k=1,l=2,m=3,n=4,d=12, wrong=13
  expect CountSuffered(1, 2, 3, 4, 12) != 13, "spec negative 1";

  // Negative 2 (scaled): k=2,l=3,m=4,n=5,d=5, wrong=5 (correct=4)
  expect CountSuffered(2, 3, 4, 5, 5) != 5, "spec negative 2";

  // Negative 3 (scaled): k=1,l=1,m=1,n=1,d=5, wrong=6 (correct=5)
  expect CountSuffered(1, 1, 1, 1, 5) != 6, "spec negative 3";

  // Negative 4: k=10,l=9,m=8,n=7,d=6, wrong=1 (correct=0)
  expect CountSuffered(10, 9, 8, 7, 6) != 1, "spec negative 4";

  // Negative 5 (scaled): k=8,l=4,m=4,n=3,d=12, wrong=7 (correct=6)
  expect CountSuffered(8, 4, 4, 3, 12) != 7, "spec negative 5";

  // Negative 6 (scaled): k=8,l=4,m=1,n=10,d=5, wrong=6 (correct=5)
  expect CountSuffered(8, 4, 1, 10, 5) != 6, "spec negative 6";

  // Negative 7 (scaled): k=4,l=1,m=8,n=7,d=5, wrong=6 (correct=5)
  expect CountSuffered(4, 1, 8, 7, 5) != 6, "spec negative 7";

  // Negative 8 (scaled): k=6,l=1,m=7,n=2,d=5, wrong=6 (correct=5)
  expect CountSuffered(6, 1, 7, 2, 5) != 6, "spec negative 8";

  // Negative 9 (scaled): k=2,l=7,m=4,n=9,d=10, wrong=8 (correct=7)
  expect CountSuffered(2, 7, 4, 9, 10) != 8, "spec negative 9";

  // Negative 10 (scaled): k=2,l=9,m=8,n=1,d=5, wrong=6 (correct=5)
  expect CountSuffered(2, 9, 8, 1, 5) != 6, "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  // Full-size test pairs using the iterative method.

  result := InsomniaCure(1, 2, 3, 4, 12);
  expect result == 12, "impl test 1 failed";

  result := InsomniaCure(2, 3, 4, 5, 24);
  expect result == 17, "impl test 2 failed";

  result := InsomniaCure(1, 1, 1, 1, 100000);
  expect result == 100000, "impl test 3 failed";

  result := InsomniaCure(10, 9, 8, 7, 6);
  expect result == 0, "impl test 4 failed";

  result := InsomniaCure(8, 4, 4, 3, 65437);
  expect result == 32718, "impl test 5 failed";

  result := InsomniaCure(8, 4, 1, 10, 59392);
  expect result == 59392, "impl test 6 failed";

  result := InsomniaCure(4, 1, 8, 7, 44835);
  expect result == 44835, "impl test 7 failed";

  result := InsomniaCure(6, 1, 7, 2, 62982);
  expect result == 62982, "impl test 8 failed";

  result := InsomniaCure(2, 7, 4, 9, 56937);
  expect result == 35246, "impl test 9 failed";

  result := InsomniaCure(2, 9, 8, 1, 75083);
  expect result == 75083, "impl test 10 failed";

  print "All tests passed\n";
}