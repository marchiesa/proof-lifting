function TotalChocolate(bought: int, a: int, b: int): int
  requires bought >= 0
  requires a > 0
{
  bought + (bought / a) * b
}

predicate IsAffordable(bought: int, s: int, c: int)
  requires c > 0
{
  bought >= 0 && bought * c <= s
}

predicate IsMaxChocolateResult(s: int, a: int, b: int, c: int, ans: int)
  requires s >= 0 && a > 0 && b >= 0 && c > 0
{
  var bought := s / c;
  IsAffordable(bought, s, c)
  && !IsAffordable(bought + 1, s, c)
  && ans == TotalChocolate(bought, a, b)
  && (bought == 0 || TotalChocolate(bought, a, b) >= TotalChocolate(bought - 1, a, b))
}

method VasyaAndChocolate(t: int, cases: seq<(int, int, int, int)>) returns (results: seq<int>)
  requires t >= 0
  requires |cases| >= t
  requires forall i | 0 <= i < t ::
    cases[i].0 >= 0 && cases[i].1 > 0 && cases[i].2 >= 0 && cases[i].3 > 0
  ensures |results| == t
  ensures forall i | 0 <= i < t ::
    IsMaxChocolateResult(cases[i].0, cases[i].1, cases[i].2, cases[i].3, results[i])
{
  results := [];
  var i := 0;
  while i < t
  {
    var (s, a, b, c) := cases[i];
    var n := s / c;
    var x := n / a;
    var ans := n + x * b;
    results := results + [ans];
    i := i + 1;
  }
}

method Main()
{
  // =============================================
  // SPEC POSITIVE TESTS (small inputs)
  // =============================================

  // Mirrors Test 1 case 1: s=10,a=3,b=1,c=1 → bought=10, ans=10+3=13
  expect IsMaxChocolateResult(10, 3, 1, 1, 13), "spec positive 1";

  // Mirrors Test 1 case 2 pattern (a=1,large b): s=5,a=1,b=3,c=1 → bought=5, ans=5+15=20
  expect IsMaxChocolateResult(5, 1, 3, 1, 20), "spec positive 2";

  // Mirrors Test 2 pattern (a=1,b=1,c=1): s=5,a=1,b=1,c=1 → bought=5, ans=5+5=10
  expect IsMaxChocolateResult(5, 1, 1, 1, 10), "spec positive 3";

  // Mirrors Test 3 case 1: s=1,a=1,b=1,c=1 → bought=1, ans=1+1=2
  expect IsMaxChocolateResult(1, 1, 1, 1, 2), "spec positive 4";

  // Mirrors Test 3 case 2 (c>s so bought=0): s=1,a=1,b=1,c=2 → bought=0, ans=0
  expect IsMaxChocolateResult(1, 1, 1, 2, 0), "spec positive 5";

  // Mirrors Test 5 pattern (large a): s=1,a=5,b=1,c=1 → bought=1, ans=1+0=1
  expect IsMaxChocolateResult(1, 5, 1, 1, 1), "spec positive 6";

  // Mirrors Test 4 pattern: s=4,a=2,b=1,c=1 → bought=4, ans=4+2=6
  expect IsMaxChocolateResult(4, 2, 1, 1, 6), "spec positive 7";

  // =============================================
  // SPEC NEGATIVE TESTS (small inputs, wrong outputs)
  // =============================================

  // Neg 1 (mirrors Negative 1: off by +1): s=10,a=3,b=1,c=1 correct=13, wrong=14
  expect !IsMaxChocolateResult(10, 3, 1, 1, 14), "spec negative 1";

  // Neg 2 (mirrors Negative 2: off by +1): s=5,a=1,b=1,c=1 correct=10, wrong=11
  expect !IsMaxChocolateResult(5, 1, 1, 1, 11), "spec negative 2";

  // Neg 3 (mirrors Negative 3: off by +1): s=1,a=1,b=1,c=1 correct=2, wrong=3
  expect !IsMaxChocolateResult(1, 1, 1, 1, 3), "spec negative 3";

  // Neg 4 (mirrors Negative 4: off by +1): s=4,a=2,b=1,c=1 correct=6, wrong=7
  expect !IsMaxChocolateResult(4, 2, 1, 1, 7), "spec negative 4";

  // Neg 5 (mirrors Negative 5: off by +1): s=1,a=5,b=1,c=1 correct=1, wrong=2
  expect !IsMaxChocolateResult(1, 5, 1, 1, 2), "spec negative 5";

  // =============================================
  // IMPLEMENTATION TESTS (full-size inputs)
  // =============================================

  // Test 1
  var r1 := VasyaAndChocolate(2, [(10, 3, 1, 1), (1000000000, 1, 1000000000, 1)]);
  expect |r1| == 2, "impl test 1 length";
  expect r1[0] == 13, "impl test 1a failed";
  expect r1[1] == 1000000001000000000, "impl test 1b failed";

  // Test 2
  var r2 := VasyaAndChocolate(1, [(19260817, 1, 1, 1)]);
  expect |r2| == 1, "impl test 2 length";
  expect r2[0] == 38521634, "impl test 2 failed";

  // Test 3
  var r3 := VasyaAndChocolate(16, [
    (1, 1, 1, 1),
    (1, 1, 1, 1000000000),
    (1, 1, 1000000000, 1),
    (1, 1, 1000000000, 1000000000),
    (1, 1000000000, 1, 1),
    (1, 1000000000, 1, 1000000000),
    (1, 1000000000, 1000000000, 1),
    (1, 1000000000, 1000000000, 1000000000),
    (1000000000, 1, 1, 1),
    (1000000000, 1, 1, 1000000000),
    (1000000000, 1, 1000000000, 1),
    (1000000000, 1, 1000000000, 1000000000),
    (1000000000, 1000000000, 1, 1),
    (1000000000, 1000000000, 1, 1000000000),
    (1000000000, 1000000000, 1000000000, 1),
    (1000000000, 1000000000, 1000000000, 1000000000)
  ]);
  expect |r3| == 16, "impl test 3 length";
  expect r3[0] == 2, "impl test 3a failed";
  expect r3[1] == 0, "impl test 3b failed";
  expect r3[2] == 1000000001, "impl test 3c failed";
  expect r3[3] == 0, "impl test 3d failed";
  expect r3[4] == 1, "impl test 3e failed";
  expect r3[5] == 0, "impl test 3f failed";
  expect r3[6] == 1, "impl test 3g failed";
  expect r3[7] == 0, "impl test 3h failed";
  expect r3[8] == 2000000000, "impl test 3i failed";
  expect r3[9] == 2, "impl test 3j failed";
  expect r3[10] == 1000000001000000000, "impl test 3k failed";
  expect r3[11] == 1000000001, "impl test 3l failed";
  expect r3[12] == 1000000001, "impl test 3m failed";
  expect r3[13] == 1, "impl test 3n failed";
  expect r3[14] == 2000000000, "impl test 3o failed";
  expect r3[15] == 1, "impl test 3p failed";

  // Test 4
  var r4 := VasyaAndChocolate(1, [(19260818, 1, 1, 1)]);
  expect |r4| == 1, "impl test 4 length";
  expect r4[0] == 38521636, "impl test 4 failed";

  // Test 5
  var r5 := VasyaAndChocolate(1, [(1, 19260817, 1, 1)]);
  expect |r5| == 1, "impl test 5 length";
  expect r5[0] == 1, "impl test 5 failed";

  print "All tests passed\n";
}