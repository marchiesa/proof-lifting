// --- Formal Specification ---

predicate IsValidPurchase(ones: int, twos: int, n: int)
{
  ones >= 0 && twos >= 0 && ones + 2 * twos == n
}

function PurchaseCost(ones: int, twos: int, a: int, b: int): int
{
  ones * a + twos * b
}

function MinCost(n: int, a: int, b: int): int
  requires n >= 0
{
  var allOnesCost := PurchaseCost(n, 0, a, b);
  var maxTwosCost := PurchaseCost(n % 2, n / 2, a, b);
  if allOnesCost <= maxTwosCost then allOnesCost else maxTwosCost
}

// --- Implementation ---

method WaterBuying(queries: seq<(int, int, int)>) returns (results: seq<int>)
  requires forall i | 0 <= i < |queries| :: queries[i].0 >= 0
  ensures |results| == |queries|
  ensures forall i | 0 <= i < |queries| ::
    results[i] == MinCost(queries[i].0, queries[i].1, queries[i].2)
{
  results := [];
  var i := 0;
  while i < |queries|
  {
    var (n, a, b) := queries[i];
    var two := 2 * a;
    var m := if two < b then two else b;
    var ans := (n / 2) * m + (n % 2) * a;
    results := results + [ans];
    i := i + 1;
  }
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Top-level ensures: results[i] == MinCost(queries[i].0, queries[i].1, queries[i].2)
  // Using small inputs (values 0-5) scaled down from each positive test pair.

  // From positive 1 (10,1,3)->10: 2a<b, allOnes wins
  expect MinCost(2, 1, 3) == 2, "spec positive 1";
  // From positive 1 (7,3,2)->9: b<2a, maxTwos wins, odd n
  expect MinCost(3, 3, 2) == 5, "spec positive 2";
  // From positive 1 (1,1000,1)->1000: n=1 odd, both strategies cost same
  expect MinCost(1, 5, 1) == 5, "spec positive 3";
  // From positive 2 (25,4,8)->100: 2a==b, even split
  expect MinCost(4, 2, 4) == 8, "spec positive 4";
  // From positive 3 (26,5,9)->117: b<2a, odd n
  expect MinCost(5, 4, 5) == 14, "spec positive 5";
  // From positive 7 (30,1,3)->30: 2a<b, allOnes wins
  expect MinCost(3, 1, 3) == 3, "spec positive 6";
  // From positive 4 (27,4,9)->108: b<2a, even n
  expect MinCost(4, 5, 4) == 8, "spec positive 7";
  // From positive 8 (31,1,6)->31: 2a<b, odd n
  expect MinCost(5, 1, 1) == 3, "spec positive 8";
  // From positive 9 (32,4,7)->112: b<2a, even n
  expect MinCost(2, 4, 5) == 5, "spec positive 9";
  // From positive 10 (33,1,56)->33: 2a<b, allOnes wins, odd n
  expect MinCost(3, 2, 5) == 6, "spec positive 10";

  // ===== SPEC NEGATIVE TESTS =====
  // Same top-level predicate with wrong outputs (correct + 1, mirroring negative pairs).

  // From negative 1: wrong output off by +1
  expect MinCost(2, 1, 3) != 3, "spec negative 1";
  // From negative 2
  expect MinCost(3, 3, 2) != 6, "spec negative 2";
  // From negative 3
  expect MinCost(1, 5, 1) != 6, "spec negative 3";
  // From negative 4
  expect MinCost(4, 2, 4) != 9, "spec negative 4";
  // From negative 5
  expect MinCost(5, 4, 5) != 15, "spec negative 5";
  // From negative 6
  expect MinCost(3, 1, 3) != 4, "spec negative 6";
  // From negative 7
  expect MinCost(4, 5, 4) != 9, "spec negative 7";
  // From negative 8
  expect MinCost(5, 1, 1) != 4, "spec negative 8";
  // From negative 9
  expect MinCost(2, 4, 5) != 6, "spec negative 9";
  // From negative 10
  expect MinCost(3, 2, 5) != 7, "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====

  // Impl test 1: 4 queries
  var r1 := WaterBuying([(10, 1, 3), (7, 3, 2), (1, 1000, 1), (1000000000000, 42, 88)]);
  expect |r1| == 4;
  expect r1[0] == 10, "impl test 1a failed";
  expect r1[1] == 9, "impl test 1b failed";
  expect r1[2] == 1000, "impl test 1c failed";
  expect r1[3] == 42000000000000, "impl test 1d failed";

  // Impl test 2
  var r2 := WaterBuying([(25, 4, 8)]);
  expect |r2| == 1;
  expect r2[0] == 100, "impl test 2 failed";

  // Impl test 3
  var r3 := WaterBuying([(26, 5, 9)]);
  expect |r3| == 1;
  expect r3[0] == 117, "impl test 3 failed";

  // Impl test 4
  var r4 := WaterBuying([(27, 4, 9)]);
  expect |r4| == 1;
  expect r4[0] == 108, "impl test 4 failed";

  // Impl test 5
  var r5 := WaterBuying([(28, 23, 53)]);
  expect |r5| == 1;
  expect r5[0] == 644, "impl test 5 failed";

  // Impl test 6
  var r6 := WaterBuying([(29, 5, 8)]);
  expect |r6| == 1;
  expect r6[0] == 117, "impl test 6 failed";

  // Impl test 7
  var r7 := WaterBuying([(30, 1, 3)]);
  expect |r7| == 1;
  expect r7[0] == 30, "impl test 7 failed";

  // Impl test 8
  var r8 := WaterBuying([(31, 1, 6)]);
  expect |r8| == 1;
  expect r8[0] == 31, "impl test 8 failed";

  // Impl test 9
  var r9 := WaterBuying([(32, 4, 7)]);
  expect |r9| == 1;
  expect r9[0] == 112, "impl test 9 failed";

  // Impl test 10
  var r10 := WaterBuying([(33, 1, 56)]);
  expect |r10| == 1;
  expect r10[0] == 33, "impl test 10 failed";

  // Impl test 11
  var r11 := WaterBuying([(34, 1, 2)]);
  expect |r11| == 1;
  expect r11[0] == 34, "impl test 11 failed";

  // Impl test 12
  var r12 := WaterBuying([(36, 1, 2)]);
  expect |r12| == 1;
  expect r12[0] == 36, "impl test 12 failed";

  // Impl test 13
  var r13 := WaterBuying([(35, 1, 2)]);
  expect |r13| == 1;
  expect r13[0] == 35, "impl test 13 failed";

  // Impl test 14
  var r14 := WaterBuying([(39, 1, 2)]);
  expect |r14| == 1;
  expect r14[0] == 39, "impl test 14 failed";

  // Impl test 15
  var r15 := WaterBuying([(40, 2, 4)]);
  expect |r15| == 1;
  expect r15[0] == 80, "impl test 15 failed";

  // Impl test 16
  var r16 := WaterBuying([(45, 6, 7)]);
  expect |r16| == 1;
  expect r16[0] == 160, "impl test 16 failed";

  // Impl test 17
  var r17 := WaterBuying([(86, 7, 90)]);
  expect |r17| == 1;
  expect r17[0] == 602, "impl test 17 failed";

  print "All tests passed\n";
}