function CansActuallyBought(x: int, a: int): int
  requires a >= 1
{
  var packs := x / a;
  var remainder := x % a;
  if 2 * remainder >= a then
    (packs + 1) * a
  else
    packs * a + remainder
}

predicate CustomerBuysMore(x: int, a: int)
  requires a >= 1
{
  CansActuallyBought(x, a) > x
}

predicate AllCustomersBuyMore(l: int, r: int, a: int)
  requires l >= 1
  requires l <= r
  requires a >= 1
{
  forall x | l <= x <= r :: CustomerBuysMore(x, a)
}

predicate SchemeExists(l: int, r: int)
  requires l >= 1
  requires l <= r
{
  exists a | 1 <= a <= 2 * r :: AllCustomersBuyMore(l, r, a)
}

method MarketingScheme(l: int, r: int) returns (result: bool)
  requires l >= 1
  requires l <= r
  ensures result == SchemeExists(l, r)
{
  result := l * 2 > r;
}

method Main()
{
  var r: bool;

  // === SPEC POSITIVE TESTS ===
  // SchemeExists(l, r) == expected, using small inputs only

  // From Test 1.1: (3,4)→true
  expect SchemeExists(3, 4) == true, "spec positive 1";
  // From Test 1.2: (1,2)→false
  expect SchemeExists(1, 2) == false, "spec positive 2";
  // From Test 1.3: (120,150)→true, scaled to (3,5)→true (2*3=6>5)
  expect SchemeExists(3, 5) == true, "spec positive 3";
  // From Test 2: (500M,1B)→false, scaled to (2,4)→false (2*2=4, not >4)
  expect SchemeExists(2, 4) == false, "spec positive 4";
  // From Test 4: (1B,1B)→true, scaled to (1,1)→true
  expect SchemeExists(1, 1) == true, "spec positive 5";
  // From Test 6.2: (500M,999999999)→true, scaled to (2,3)→true (2*2=4>3)
  expect SchemeExists(2, 3) == true, "spec positive 6";
  // From Test 7.4: (49999999,99999999)→false, scaled to (1,3)→false (2*1=2<3)
  expect SchemeExists(1, 3) == false, "spec positive 7";
  // From Test 8: (999999999,1B)→true, scaled to (4,5)→true (2*4=8>5)
  expect SchemeExists(4, 5) == true, "spec positive 8";
  // From Test 10: (10485760,20971520)→false, scaled to (2,5)→false (2*2=4<5)
  expect SchemeExists(2, 5) == false, "spec positive 9";
  // From Test 4 pattern: same-value, (5,5)→true
  expect SchemeExists(5, 5) == true, "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // Wrong outputs must not satisfy the ensures predicate

  // From Neg 2: correct=false, wrong=true; scaled to (2,4)
  expect !(true == SchemeExists(2, 4)), "spec negative 1";
  // From Neg 3: correct=false, wrong=true; scaled to (1,2)
  expect !(true == SchemeExists(1, 2)), "spec negative 2";
  // From Neg 4: correct=true, wrong=false; scaled to (1,1)
  expect !(false == SchemeExists(1, 1)), "spec negative 3";
  // From Neg 5: correct=true, wrong=false; scaled to (3,5)
  expect !(false == SchemeExists(3, 5)), "spec negative 4";
  // From Neg 8: correct=true, wrong=false; scaled to (4,5)
  expect !(false == SchemeExists(4, 5)), "spec negative 5";
  // From Neg 10: correct=false, wrong=true; scaled to (2,5)
  expect !(true == SchemeExists(2, 5)), "spec negative 6";
  // From Neg 1: (120,150) correct=true, wrong=false; scaled to (3,4)
  expect !(false == SchemeExists(3, 4)), "spec negative 7";
  // From Neg 6: last case correct=false, wrong=true; scaled to (1,3)
  expect !(true == SchemeExists(1, 3)), "spec negative 8";
  // From Neg 7: last case correct=false, wrong=true; scaled to (3,6) (2*3=6, not >6)
  expect !(true == SchemeExists(3, 6)), "spec negative 9";
  // From Neg 9: second case correct=false, wrong=true; scaled to (2,3) true→wrong false
  expect !(false == SchemeExists(2, 3)), "spec negative 10";

  // === IMPLEMENTATION TESTS ===

  // Test 1
  r := MarketingScheme(3, 4);
  expect r == true, "impl test 1.1 failed";
  r := MarketingScheme(1, 2);
  expect r == false, "impl test 1.2 failed";
  r := MarketingScheme(120, 150);
  expect r == true, "impl test 1.3 failed";

  // Test 2
  r := MarketingScheme(500000000, 1000000000);
  expect r == false, "impl test 2.1 failed";

  // Test 3
  r := MarketingScheme(100000001, 200000002);
  expect r == false, "impl test 3.1 failed";

  // Test 4
  r := MarketingScheme(1000000000, 1000000000);
  expect r == true, "impl test 4.1 failed";

  // Test 5
  r := MarketingScheme(100000000, 199999999);
  expect r == true, "impl test 5.1 failed";

  // Test 6
  r := MarketingScheme(500000000, 1000000000);
  expect r == false, "impl test 6.1 failed";
  r := MarketingScheme(500000000, 999999999);
  expect r == true, "impl test 6.2 failed";
  r := MarketingScheme(499999998, 999999996);
  expect r == false, "impl test 6.3 failed";
  r := MarketingScheme(499999998, 999999995);
  expect r == true, "impl test 6.4 failed";
  r := MarketingScheme(499999998, 999999997);
  expect r == false, "impl test 6.5 failed";

  // Test 7
  r := MarketingScheme(50000000, 100000000);
  expect r == false, "impl test 7.1 failed";
  r := MarketingScheme(50000001, 100000000);
  expect r == true, "impl test 7.2 failed";
  r := MarketingScheme(50000000, 99999999);
  expect r == true, "impl test 7.3 failed";
  r := MarketingScheme(49999999, 99999999);
  expect r == false, "impl test 7.4 failed";

  // Test 8
  r := MarketingScheme(999999999, 1000000000);
  expect r == true, "impl test 8.1 failed";

  // Test 9
  r := MarketingScheme(500000001, 1000000000);
  expect r == true, "impl test 9.1 failed";
  r := MarketingScheme(500000000, 1000000000);
  expect r == false, "impl test 9.2 failed";

  // Test 10
  r := MarketingScheme(10485760, 20971520);
  expect r == false, "impl test 10.1 failed";

  // Test 11
  r := MarketingScheme(499999999, 999999998);
  expect r == false, "impl test 11.1 failed";
  r := MarketingScheme(499999999, 999999997);
  expect r == true, "impl test 11.2 failed";

  // Test 12
  r := MarketingScheme(20971520, 41943040);
  expect r == false, "impl test 12.1 failed";

  // Test 13
  r := MarketingScheme(109999999, 219999998);
  expect r == false, "impl test 13.1 failed";

  // Test 14
  r := MarketingScheme(500000000, 999999999);
  expect r == true, "impl test 14.1 failed";

  // Test 15
  r := MarketingScheme(500000000, 1000000000);
  expect r == false, "impl test 15.1 failed";
  r := MarketingScheme(101, 202);
  expect r == false, "impl test 15.2 failed";
  r := MarketingScheme(102, 204);
  expect r == false, "impl test 15.3 failed";
  r := MarketingScheme(102, 205);
  expect r == false, "impl test 15.4 failed";
  r := MarketingScheme(500000001, 1000000000);
  expect r == true, "impl test 15.5 failed";
  r := MarketingScheme(101, 200);
  expect r == true, "impl test 15.6 failed";
  r := MarketingScheme(101, 201);
  expect r == true, "impl test 15.7 failed";
  r := MarketingScheme(102, 203);
  expect r == true, "impl test 15.8 failed";

  // Test 16
  r := MarketingScheme(54345457, 108690913);
  expect r == true, "impl test 16.1 failed";

  // Test 17
  r := MarketingScheme(335544320, 671088640);
  expect r == false, "impl test 17.1 failed";

  // Test 18
  r := MarketingScheme(335544321, 671088639);
  expect r == true, "impl test 18.1 failed";

  // Test 19
  r := MarketingScheme(54345456, 108690913);
  expect r == false, "impl test 19.1 failed";

  // Test 20
  r := MarketingScheme(335544322, 671088639);
  expect r == true, "impl test 20.1 failed";

  print "All tests passed\n";
}