function Outcome(r: int, buyPrice: int, sellPrice: int, shares: int): int
{
  r - shares * buyPrice + shares * sellPrice
}

predicate ValidTrade(r: int, buyPrice: int, shares: int)
{
  buyPrice > 0 && shares >= 0 && shares * buyPrice <= r
}

predicate IsAchievable(result: int, r: int, s: seq<int>, b: seq<int>)
{
  result == r
  ||
  (exists i | 0 <= i < |s| :: exists j | 0 <= j < |b| :: exists k | 0 <= k <= r ::
    ValidTrade(r, s[i], k) && result == Outcome(r, s[i], b[j], k))
}

predicate IsOptimal(result: int, r: int, s: seq<int>, b: seq<int>)
{
  result >= r
  &&
  (forall i | 0 <= i < |s| :: forall j | 0 <= j < |b| :: forall k | 0 <= k <= r ::
    ValidTrade(r, s[i], k) ==> Outcome(r, s[i], b[j], k) <= result)
}

method StockArbitraging(n: int, m: int, r: int, s: seq<int>, b: seq<int>) returns (maxBourles: int)
  requires |s| == n && n >= 1
  requires |b| == m && m >= 1
  requires r >= 1
  requires forall i | 0 <= i < n :: s[i] >= 1
  requires forall j | 0 <= j < m :: b[j] >= 1
  ensures IsAchievable(maxBourles, r, s, b)
  ensures IsOptimal(maxBourles, r, s, b)
{
  var minS := s[0];
  var i := 1;
  while i < |s|
  {
    if s[i] < minS {
      minS := s[i];
    }
    i := i + 1;
  }

  var maxB := b[0];
  i := 1;
  while i < |b|
  {
    if b[i] > maxB {
      maxB := b[i];
    }
    i := i + 1;
  }

  var profit := r % minS + (r / minS) * maxB;
  if profit > r {
    maxBourles := profit;
  } else {
    maxBourles := r;
  }
}

method Main()
{
  // =============================================
  // SPEC POSITIVE TESTS (small inputs, correct outputs)
  // Each tests both ensures predicates: IsAchievable AND IsOptimal
  // =============================================

  // SP1: Equivalent to Test 3 — r=1, buy=sell=1, result=r
  expect IsAchievable(1, 1, [1], [1]), "spec pos 1 achievable";
  expect IsOptimal(1, 1, [1], [1]), "spec pos 1 optimal";

  // SP2: Equivalent to Test 1 — buy low at 2, sell high at 5
  // r=4, shares=2, profit=4-4+10=10
  expect IsAchievable(10, 4, [2], [5]), "spec pos 2 achievable";
  expect IsOptimal(10, 4, [2], [5]), "spec pos 2 optimal";

  // SP3: Equivalent to Test 2 — sell price < buy price, no profitable trade
  // r=3, s=[5], b=[2] → can't afford any shares, result=3
  expect IsAchievable(3, 3, [5], [2]), "spec pos 3 achievable";
  expect IsOptimal(3, 3, [5], [2]), "spec pos 3 optimal";

  // SP4: Equivalent to Test 4 — profitable with remainder
  // r=5, s=[2], b=[3] → shares=2, profit=1+6=7
  expect IsAchievable(7, 5, [2], [3]), "spec pos 4 achievable";
  expect IsOptimal(7, 5, [2], [3]), "spec pos 4 optimal";

  // SP5: Equivalent to Test 5 — evenly divisible
  // r=4, s=[2], b=[3] → shares=2, profit=0+6=6
  expect IsAchievable(6, 4, [2], [3]), "spec pos 5 achievable";
  expect IsOptimal(6, 4, [2], [3]), "spec pos 5 optimal";

  // SP6: Equivalent to Test 6 — multiple prices, pick cheapest buy & highest sell
  // r=3, s=[5,2], b=[1,4] → minS=2, maxB=4, shares=1, profit=1+4=5
  expect IsAchievable(5, 3, [5, 2], [1, 4]), "spec pos 6 achievable";
  expect IsOptimal(5, 3, [5, 2], [1, 4]), "spec pos 6 optimal";

  // SP7: Equivalent to Test 7 — buy at 1, sell high
  // r=3, s=[2,1], b=[2,5] → shares=3, profit=0+15=15
  expect IsAchievable(15, 3, [2, 1], [2, 5]), "spec pos 7 achievable";
  expect IsOptimal(15, 3, [2, 1], [2, 5]), "spec pos 7 optimal";

  // SP8: Equivalent to Test 14 — can't afford any shares
  // r=2, s=[5], b=[5] → can't buy, result=2
  expect IsAchievable(2, 2, [5], [5]), "spec pos 8 achievable";
  expect IsOptimal(2, 2, [5], [5]), "spec pos 8 optimal";

  // =============================================
  // SPEC NEGATIVE TESTS (small inputs, wrong outputs)
  // Tests that the ensures conjunction FAILS for wrong outputs
  // =============================================

  // SN1: Scaled from Neg 3 — wrong=2 (correct=1), too high, not achievable
  expect !(IsAchievable(2, 1, [1], [1]) && IsOptimal(2, 1, [1], [1])), "spec neg 1";

  // SN2: Scaled from Neg 1 — wrong=11 (correct=10), too high, not achievable
  expect !(IsAchievable(11, 4, [2], [5]) && IsOptimal(11, 4, [2], [5])), "spec neg 2";

  // SN3: Scaled from Neg 2 — wrong=4 (correct=3), too high, not achievable
  expect !(IsAchievable(4, 3, [5], [2]) && IsOptimal(4, 3, [5], [2])), "spec neg 3";

  // SN4: Scaled from Neg 4 — wrong=8 (correct=7), too high, not achievable
  expect !(IsAchievable(8, 5, [2], [3]) && IsOptimal(8, 5, [2], [3])), "spec neg 4";

  // SN5: Scaled from Neg 5 — wrong=7 (correct=6), too high, not achievable
  expect !(IsAchievable(7, 4, [2], [3]) && IsOptimal(7, 4, [2], [3])), "spec neg 5";

  // SN6: Scaled from Neg 6 — wrong=6 (correct=5), too high, not achievable
  expect !(IsAchievable(6, 3, [5, 2], [1, 4]) && IsOptimal(6, 3, [5, 2], [1, 4])), "spec neg 6";

  // SN7: Scaled from Neg 7 — wrong=16 (correct=15), too high, not achievable
  expect !(IsAchievable(16, 3, [2, 1], [2, 5]) && IsOptimal(16, 3, [2, 1], [2, 5])), "spec neg 7";

  // SN8: Scaled from Neg 10 — wrong=3 (correct=2), too high, not achievable
  expect !(IsAchievable(3, 2, [5], [5]) && IsOptimal(3, 2, [5], [5])), "spec neg 8";

  // SN9: Wrong=7 (correct=10), too LOW — achievable at k=1 but NOT optimal (k=2 gives 10)
  expect !(IsAchievable(7, 4, [2], [5]) && IsOptimal(7, 4, [2], [5])), "spec neg 9";

  // SN10: Wrong=6 (correct=15), too LOW — achievable but NOT optimal (k=3 gives 15)
  expect !(IsAchievable(6, 3, [2, 1], [2, 5]) && IsOptimal(6, 3, [2, 1], [2, 5])), "spec neg 10";

  // =============================================
  // IMPLEMENTATION TESTS (full-size test pairs)
  // =============================================

  var r1 := StockArbitraging(3, 4, 11, [4, 2, 5], [4, 4, 5, 4]);
  expect r1 == 26, "impl test 1 failed";

  var r2 := StockArbitraging(2, 2, 50, [5, 7], [4, 2]);
  expect r2 == 50, "impl test 2 failed";

  var r3 := StockArbitraging(1, 1, 1, [1], [1]);
  expect r3 == 1, "impl test 3 failed";

  var r4 := StockArbitraging(1, 1, 35, [5], [7]);
  expect r4 == 49, "impl test 4 failed";

  var r5 := StockArbitraging(1, 1, 36, [5], [7]);
  expect r5 == 50, "impl test 5 failed";

  var r6 := StockArbitraging(3, 5, 20, [1000, 4, 6], [1, 2, 7, 6, 5]);
  expect r6 == 35, "impl test 6 failed";

  var r7 := StockArbitraging(5, 3, 20, [5, 4, 3, 2, 1], [6, 7, 1000]);
  expect r7 == 20000, "impl test 7 failed";

  var r8 := StockArbitraging(30, 30, 987,
    [413, 937, 166, 77, 749, 925, 792, 353, 773, 88, 218, 863, 71, 186, 753, 306, 952, 966, 236, 501, 84, 163, 767, 99, 887, 380, 435, 888, 589, 761],
    [68, 501, 323, 916, 506, 952, 411, 813, 664, 49, 860, 151, 120, 543, 168, 944, 302, 521, 245, 517, 464, 734, 205, 235, 173, 893, 109, 655, 346, 837]);
  expect r8 == 12440, "impl test 8 failed";

  var r9 := StockArbitraging(30, 22, 1000,
    [999, 953, 947, 883, 859, 857, 775, 766, 723, 713, 696, 691, 659, 650, 597, 474, 472, 456, 455, 374, 367, 354, 347, 215, 111, 89, 76, 76, 59, 55],
    [172, 188, 223, 247, 404, 445, 449, 489, 493, 554, 558, 587, 588, 627, 686, 714, 720, 744, 747, 786, 830, 953]);
  expect r9 == 17164, "impl test 9 failed";

  var r10 := StockArbitraging(28, 29, 1000,
    [555, 962, 781, 562, 856, 700, 628, 591, 797, 873, 950, 607, 526, 513, 552, 954, 768, 823, 863, 650, 984, 653, 741, 548, 676, 577, 625, 902],
    [185, 39, 223, 383, 221, 84, 165, 492, 79, 53, 475, 410, 314, 489, 59, 138, 395, 346, 91, 258, 14, 354, 410, 25, 41, 394, 463, 432, 325]);
  expect r10 == 1000, "impl test 10 failed";

  var r11 := StockArbitraging(30, 29, 999,
    [993, 982, 996, 992, 988, 984, 981, 982, 981, 981, 992, 997, 982, 996, 995, 981, 995, 982, 994, 996, 988, 986, 990, 991, 987, 993, 1000, 989, 998, 991],
    [19, 12, 14, 5, 20, 11, 15, 11, 7, 14, 12, 8, 1, 9, 7, 15, 6, 20, 15, 20, 17, 15, 20, 1, 4, 13, 2, 2, 17]);
  expect r11 == 999, "impl test 11 failed";

  var r12 := StockArbitraging(30, 30, 999,
    [19, 8, 6, 1, 4, 12, 14, 12, 8, 14, 14, 2, 13, 11, 10, 15, 13, 14, 2, 5, 15, 17, 18, 16, 9, 4, 2, 14, 12, 9],
    [993, 987, 993, 998, 998, 987, 980, 986, 995, 987, 998, 989, 981, 982, 983, 981, 997, 991, 989, 989, 993, 990, 984, 997, 995, 984, 982, 994, 990, 984]);
  expect r12 == 997002, "impl test 12 failed";

  var r13 := StockArbitraging(28, 30, 1000,
    [185, 184, 177, 171, 165, 162, 162, 154, 150, 136, 133, 127, 118, 111, 106, 106, 95, 92, 86, 85, 77, 66, 65, 40, 28, 10, 10, 4],
    [305, 309, 311, 313, 319, 321, 323, 338, 349, 349, 349, 351, 359, 373, 378, 386, 405, 409, 420, 445, 457, 462, 463, 466, 466, 471, 473, 479, 479, 482]);
  expect r13 == 120500, "impl test 13 failed";

  var r14 := StockArbitraging(1, 1, 10, [11], [1000]);
  expect r14 == 10, "impl test 14 failed";

  var r15 := StockArbitraging(29, 30, 989,
    [450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450],
    [451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451, 451]);
  expect r15 == 991, "impl test 15 failed";

  var r16 := StockArbitraging(25, 30, 989,
    [153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153],
    [153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153]);
  expect r16 == 989, "impl test 16 failed";

  var r17 := StockArbitraging(30, 26, 997,
    [499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499, 499],
    [384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384]);
  expect r17 == 997, "impl test 17 failed";

  var r18 := StockArbitraging(30, 30, 1000,
    [1, 4, 2, 2, 2, 1, 2, 2, 2, 3, 3, 3, 1, 4, 2, 4, 3, 1, 2, 2, 3, 2, 4, 2, 3, 4, 2, 4, 3, 2],
    [1000, 999, 997, 1000, 999, 998, 999, 999, 1000, 1000, 997, 997, 999, 997, 999, 997, 997, 999, 1000, 999, 997, 998, 998, 998, 997, 997, 999, 1000, 998, 998]);
  expect r18 == 1000000, "impl test 18 failed";

  var r19 := StockArbitraging(30, 29, 42,
    [632, 501, 892, 532, 293, 47, 45, 669, 129, 616, 322, 92, 812, 499, 205, 115, 889, 442, 589, 34, 681, 944, 49, 546, 134, 625, 937, 179, 1000, 69],
    [837, 639, 443, 361, 323, 493, 639, 573, 645, 55, 711, 190, 905, 628, 627, 278, 967, 926, 398, 479, 71, 829, 960, 916, 360, 43, 341, 337, 90]);
  expect r19 == 975, "impl test 19 failed";

  var r20 := StockArbitraging(30, 30, 1000,
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [962, 987, 940, 905, 911, 993, 955, 994, 984, 994, 923, 959, 923, 993, 959, 925, 922, 909, 932, 911, 994, 1000, 994, 976, 915, 979, 928, 999, 993, 956]);
  expect r20 == 1000000, "impl test 20 failed";

  print "All tests passed\n";
}