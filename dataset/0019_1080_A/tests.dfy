predicate SufficientNotebooks(r: int, g: int, b: int, n: int, k: int)
{
  r >= 0 && g >= 0 && b >= 0 &&
  r * k >= 2 * n &&
  g * k >= 5 * n &&
  b * k >= 8 * n
}

predicate IsMinCover(m: int, need: int, k: int)
  requires k >= 1
{
  m >= 0 &&
  m * k >= need &&
  (m == 0 || (m - 1) * k < need)
}

predicate IsMinTotalNotebooks(total: int, n: int, k: int)
  requires n >= 1 && k >= 1
{
  exists r | 0 <= r <= 2 * n ::
    exists g | 0 <= g <= 5 * n ::
      exists b | 0 <= b <= 8 * n ::
        IsMinCover(r, 2 * n, k) &&
        IsMinCover(g, 5 * n, k) &&
        IsMinCover(b, 8 * n, k) &&
        SufficientNotebooks(r, g, b, n, k) &&
        total == r + g + b
}

method PetyaAndOrigami(n: int, k: int) returns (notebooks: int)
  requires n >= 1 && k >= 1
  ensures IsMinTotalNotebooks(notebooks, n, k)
{
  notebooks := ((n * 2 + k - 1) / k) + ((n * 5 + k - 1) / k) + ((n * 8 + k - 1) / k);
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Small inputs where bounded existential quantifier enumeration is feasible.
  // Bounds are (2n+1)*(5n+1)*(8n+1) iterations.

  // n=1, k=1 => 2+5+8 = 15  (from test pair 3)
  expect IsMinTotalNotebooks(15, 1, 1), "spec positive 1";

  // n=3, k=5 => ceil(6/5)+ceil(15/5)+ceil(24/5) = 2+3+5 = 10  (from test pair 1)
  expect IsMinTotalNotebooks(10, 3, 5), "spec positive 2";

  // n=1, k=100000000 => 1+1+1 = 3  (from test pair 5; n=1 so bounds are tiny)
  expect IsMinTotalNotebooks(3, 1, 100000000), "spec positive 3";

  // n=1, k=2 => 1+3+4 = 8
  expect IsMinTotalNotebooks(8, 1, 2), "spec positive 4";

  // n=1, k=5 => 1+1+2 = 4
  expect IsMinTotalNotebooks(4, 1, 5), "spec positive 5";

  // n=2, k=3 => 2+4+6 = 12
  expect IsMinTotalNotebooks(12, 2, 3), "spec positive 6";

  // n=2, k=1 => 4+10+16 = 30
  expect IsMinTotalNotebooks(30, 2, 1), "spec positive 7";

  // === SPEC NEGATIVE TESTS ===
  // Wrong outputs that the spec must reject (exhaustive enumeration finds no witness).

  // n=1, k=1, wrong=16 (correct=15)  (from neg pair 3)
  expect !IsMinTotalNotebooks(16, 1, 1), "spec negative 1";

  // n=3, k=5, wrong=11 (correct=10)  (from neg pair 1)
  expect !IsMinTotalNotebooks(11, 3, 5), "spec negative 2";

  // n=1, k=100000000, wrong=4 (correct=3)  (from neg pair 5)
  expect !IsMinTotalNotebooks(4, 1, 100000000), "spec negative 3";

  // n=1, k=2, wrong=9 (correct=8)
  expect !IsMinTotalNotebooks(9, 1, 2), "spec negative 4";

  // n=1, k=5, wrong=5 (correct=4)
  expect !IsMinTotalNotebooks(5, 1, 5), "spec negative 5";

  // n=2, k=3, wrong=13 (correct=12)
  expect !IsMinTotalNotebooks(13, 2, 3), "spec negative 6";

  // n=2, k=1, wrong=31 (correct=30)
  expect !IsMinTotalNotebooks(31, 2, 1), "spec negative 7";

  // === IMPLEMENTATION TESTS ===
  var result: int;

  result := PetyaAndOrigami(3, 5);
  expect result == 10, "impl test 1 failed";

  result := PetyaAndOrigami(15, 6);
  expect result == 38, "impl test 2 failed";

  result := PetyaAndOrigami(1, 1);
  expect result == 15, "impl test 3 failed";

  result := PetyaAndOrigami(100000000, 1);
  expect result == 1500000000, "impl test 4 failed";

  result := PetyaAndOrigami(1, 100000000);
  expect result == 3, "impl test 5 failed";

  result := PetyaAndOrigami(96865066, 63740710);
  expect result == 25, "impl test 6 failed";

  result := PetyaAndOrigami(58064619, 65614207);
  expect result == 15, "impl test 7 failed";

  result := PetyaAndOrigami(31115339, 39163052);
  expect result == 13, "impl test 8 failed";

  result := PetyaAndOrigami(14231467, 12711896);
  expect result == 18, "impl test 9 failed";

  result := PetyaAndOrigami(92314891, 81228036);
  expect result == 19, "impl test 10 failed";

  print "All tests passed\n";
}