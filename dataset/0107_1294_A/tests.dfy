predicate ValidDistribution(a: int, b: int, c: int, n: int, A: int, B: int, C: int)
{
  A >= 0 && B >= 0 && C >= 0
  && A + B + C == n
  && a + A == b + B
  && a + A == c + C
}

predicate CanDistribute(a: int, b: int, c: int, n: int)
  requires n >= 0
{
  exists A: int, B: int, C: int
    | 0 <= A <= n && 0 <= B <= n && 0 <= C <= n
    :: ValidDistribution(a, b, c, n, A, B, C)
}

method CollectingCoins(a: int, b: int, c: int, n: int) returns (result: bool)
  requires a >= 0 && b >= 0 && c >= 0 && n >= 0
  ensures result == CanDistribute(a, b, c, n)
{
  var tot := a + b + c + n;
  if tot % 3 != 0 {
    return false;
  }
  var des := tot / 3;
  if a > des || b > des || c > des {
    return false;
  }
  return true;
}

method Main()
{
  // ==========================================
  // SPEC POSITIVE TESTS (small inputs only)
  // ==========================================

  // From Test 7: (1,1,1,3) → true
  expect CanDistribute(1, 1, 1, 3) == true, "spec positive 1";

  // From Test 9: (1,2,3,3) → true
  expect CanDistribute(1, 2, 3, 3) == true, "spec positive 2";

  // From Test 4: (5,5,5,3) → true
  expect CanDistribute(5, 5, 5, 3) == true, "spec positive 3";

  // From Test 12: (1,1,1,1) → false
  expect CanDistribute(1, 1, 1, 1) == false, "spec positive 4";

  // Scaled from Test 1 (5,3,2,8): (2,1,0,3) → true
  expect CanDistribute(2, 1, 0, 3) == true, "spec positive 5";

  // Scaled from Test 3 (3,798,437,1804): (0,1,2,3) → true
  expect CanDistribute(0, 1, 2, 3) == true, "spec positive 6";

  // Scaled from Test 6 (10,10,10,1): (1,1,1,2) → false
  expect CanDistribute(1, 1, 1, 2) == false, "spec positive 7";

  // From Test 5: (1,2,3,6) → true
  expect CanDistribute(1, 2, 3, 6) == true, "spec positive 8";

  // ==========================================
  // SPEC NEGATIVE TESTS (small inputs only)
  // ==========================================

  // Negative 2: (1,1,1,1111) wrong=true. Scaled: (1,1,1,2), wrong=true
  expect !(CanDistribute(1, 1, 1, 2) == true), "spec negative 2";

  // Negative 4: (5,5,5,3) wrong=false
  expect !(CanDistribute(5, 5, 5, 3) == false), "spec negative 4";

  // Negative 7: (1,1,1,3) wrong=false
  expect !(CanDistribute(1, 1, 1, 3) == false), "spec negative 7";

  // Negative 9: (1,2,3,3) wrong=false
  expect !(CanDistribute(1, 2, 3, 3) == false), "spec negative 9";

  // Negative 6: (10,10,10,1) wrong=true. Scaled: (2,2,2,1), wrong=true
  expect !(CanDistribute(2, 2, 2, 1) == true), "spec negative 6";

  // Negative 10: (10,20,30,50) wrong=true. Scaled: (1,2,3,2), wrong=true
  expect !(CanDistribute(1, 2, 3, 2) == true), "spec negative 10";

  // Negative 5: (1,2,3,6) wrong=false
  expect !(CanDistribute(1, 2, 3, 6) == false), "spec negative 5";

  // Negative 3: (3,798,437,1804) wrong=false. Scaled: (0,1,2,3), wrong=false
  expect !(CanDistribute(0, 1, 2, 3) == false), "spec negative 3";

  // Negative 8: (3,7,5,9) wrong=false. Scaled: (1,2,1,2), wrong=false
  expect !(CanDistribute(1, 2, 1, 2) == false), "spec negative 8";

  // ==========================================
  // IMPLEMENTATION TESTS (full-size inputs)
  // ==========================================

  var r1 := CollectingCoins(5, 3, 2, 8);
  expect r1 == true, "impl test 1 failed";

  var r2 := CollectingCoins(100, 101, 102, 105);
  expect r2 == true, "impl test 2 failed";

  var r3 := CollectingCoins(3, 2, 1, 100000000);
  expect r3 == false, "impl test 3 failed";

  var r4 := CollectingCoins(10, 20, 15, 14);
  expect r4 == false, "impl test 4 failed";

  var r5 := CollectingCoins(101, 101, 101, 3);
  expect r5 == true, "impl test 5 failed";

  var r6 := CollectingCoins(1, 1, 1, 1111);
  expect r6 == false, "impl test 6 failed";

  var r7 := CollectingCoins(3, 798, 437, 1804);
  expect r7 == true, "impl test 7 failed";

  var r8 := CollectingCoins(5, 5, 5, 3);
  expect r8 == true, "impl test 8 failed";

  var r9 := CollectingCoins(1, 2, 3, 6);
  expect r9 == true, "impl test 9 failed";

  var r10 := CollectingCoins(10, 10, 10, 1);
  expect r10 == false, "impl test 10 failed";

  var r11 := CollectingCoins(1, 1, 1, 3);
  expect r11 == true, "impl test 11 failed";

  var r12 := CollectingCoins(3, 7, 5, 9);
  expect r12 == true, "impl test 12 failed";

  var r13 := CollectingCoins(1, 2, 3, 3);
  expect r13 == true, "impl test 13 failed";

  var r14 := CollectingCoins(10, 20, 30, 50);
  expect r14 == false, "impl test 14 failed";

  var r15 := CollectingCoins(5, 5, 5, 15);
  expect r15 == true, "impl test 15 failed";

  var r16 := CollectingCoins(1, 1, 1, 1);
  expect r16 == false, "impl test 16 failed";

  var r17 := CollectingCoins(8, 4, 2, 10);
  expect r17 == true, "impl test 17 failed";

  print "All tests passed\n";
}