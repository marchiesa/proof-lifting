predicate ValidAllocation(b: int, p: int, f: int, ham: int, chicken: int)
{
  ham >= 0 && chicken >= 0 &&
  ham <= p && chicken <= f &&
  2 * ham + 2 * chicken <= b
}

function AllocationProfit(ham: int, chicken: int, h: int, c: int): int
{
  ham * h + chicken * c
}

predicate IsMaxProfit(b: int, p: int, f: int, h: int, c: int, profit: int)
{
  (exists ham | 0 <= ham <= p ::
    exists chicken | 0 <= chicken <= f ::
      ValidAllocation(b, p, f, ham, chicken) &&
      AllocationProfit(ham, chicken, h, c) == profit)
  &&
  (forall ham | 0 <= ham <= p ::
    forall chicken | 0 <= chicken <= f ::
      !ValidAllocation(b, p, f, ham, chicken) ||
      AllocationProfit(ham, chicken, h, c) <= profit)
}

method MaxProfit(b: int, p: int, f: int, h: int, c: int) returns (profit: int)
  requires b >= 0 && p >= 0 && f >= 0 && h >= 0 && c >= 0
  ensures IsMaxProfit(b, p, f, h, c, profit)
{
  var lb := b;
  var lp := p;
  var lf := f;
  var lh := h;
  var lc := c;

  if lh < lc {
    var tmp := lh;
    lh := lc;
    lc := tmp;
    tmp := lp;
    lp := lf;
    lf := tmp;
  }

  var ham := lp;
  if lb / 2 < ham {
    ham := lb / 2;
  }
  profit := ham * lh;
  lb := lb - 2 * ham;

  var chicken := lf;
  if lb / 2 < chicken {
    chicken := lb / 2;
  }
  profit := profit + chicken * lc;
}

method Main()
{
  var result: int;

  // === SPEC POSITIVE TESTS ===
  // From Test 1.1: (15,2,3,5,10)->40. p=2,f=3: 3*4=12 combos, small.
  expect IsMaxProfit(15, 2, 3, 5, 10, 40), "spec positive 1";
  // From Test 1.2: (7,5,2,10,12)->34. p=5,f=2: 6*3=18 combos, small.
  expect IsMaxProfit(7, 5, 2, 10, 12, 34), "spec positive 2";
  // From Test 1.3/2.1 scaled: (1,100,100,100,100)->0 scaled to (1,1,1,1,1)->0. p=1,f=1.
  expect IsMaxProfit(1, 1, 1, 1, 1, 0), "spec positive 3";
  // From Test 2.4 scaled: (100,1,1,100,100)->200 scaled to (4,1,1,3,3)->6. p=1,f=1.
  expect IsMaxProfit(4, 1, 1, 3, 3, 6), "spec positive 4";
  // From Test 3.1: (18,6,4,3,4)->31. p=6,f=4: 7*5=35 combos, OK.
  expect IsMaxProfit(18, 6, 4, 3, 4, 31), "spec positive 5";
  // From Test 2.5 scaled: (100,50,50,100,99)->5000 scaled to (4,1,1,5,4)->9. p=1,f=1.
  expect IsMaxProfit(4, 1, 1, 5, 4, 9), "spec positive 6";
  // Edge case: no ingredients at all -> 0. p=0,f=0.
  expect IsMaxProfit(0, 0, 0, 5, 3, 0), "spec positive 7";

  // === SPEC NEGATIVE TESTS ===
  // From Negative 1: (15,2,3,5,10) wrong=41, correct=40. p=2,f=3.
  expect !IsMaxProfit(15, 2, 3, 5, 10, 41), "spec negative 1";
  // From Negative 2: (1,1,1,1,1) wrong=1, correct=0. p=1,f=1.
  expect !IsMaxProfit(1, 1, 1, 1, 1, 1), "spec negative 2";
  // From Negative 3: (18,6,4,3,4) wrong=32, correct=31. p=6,f=4.
  expect !IsMaxProfit(18, 6, 4, 3, 4, 32), "spec negative 3";
  // Derived from Test 1.2: off-by-one, 35 vs correct 34. p=5,f=2.
  expect !IsMaxProfit(7, 5, 2, 10, 12, 35), "spec negative 4";
  // Derived: (2,1,1,5,3) suboptimal profit 3 (correct max is 5). p=1,f=1.
  expect !IsMaxProfit(2, 1, 1, 5, 3, 3), "spec negative 5";
  // Derived: (0,0,0,5,3) wrong=1, correct=0. p=0,f=0.
  expect !IsMaxProfit(0, 0, 0, 5, 3, 1), "spec negative 6";

  // === IMPLEMENTATION TESTS ===
  // Test 1
  result := MaxProfit(15, 2, 3, 5, 10);
  expect result == 40, "impl test 1.1 failed";

  result := MaxProfit(7, 5, 2, 10, 12);
  expect result == 34, "impl test 1.2 failed";

  result := MaxProfit(1, 100, 100, 100, 100);
  expect result == 0, "impl test 1.3 failed";

  // Test 2
  result := MaxProfit(1, 1, 1, 1, 1);
  expect result == 0, "impl test 2.1 failed";

  result := MaxProfit(100, 100, 100, 100, 100);
  expect result == 5000, "impl test 2.2 failed";

  result := MaxProfit(1, 100, 100, 100, 100);
  expect result == 0, "impl test 2.3 failed";

  result := MaxProfit(100, 1, 1, 100, 100);
  expect result == 200, "impl test 2.4 failed";

  result := MaxProfit(100, 50, 50, 100, 99);
  expect result == 5000, "impl test 2.5 failed";

  result := MaxProfit(100, 51, 51, 100, 99);
  expect result == 5000, "impl test 2.6 failed";

  result := MaxProfit(99, 51, 51, 100, 99);
  expect result == 4900, "impl test 2.7 failed";

  // Test 3
  result := MaxProfit(18, 6, 4, 3, 4);
  expect result == 31, "impl test 3.1 failed";

  print "All tests passed\n";
}