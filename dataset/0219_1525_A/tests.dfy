// --- Specification predicates ---

predicate Divides(d: int, n: int)
{
  d > 0 && n % d == 0
}

predicate IsGcd(g: int, a: int, b: int)
{
  g > 0 && a > 0 && b > 0 &&
  Divides(g, a) && Divides(g, b) &&
  forall d | 1 <= d <= a :: (Divides(d, a) && Divides(d, b)) ==> d <= g
}

predicate IsValidPotion(e: int, w: int, k: int)
{
  e >= 0 && w >= 0 && e + w > 0 && e * 100 == k * (e + w)
}

predicate AchievableInSteps(steps: int, k: int)
{
  steps >= 0 &&
  exists e | 0 <= e <= steps :: IsValidPotion(e, steps - e, k)
}

predicate IsMinSteps(steps: int, k: int)
{
  steps >= 1 &&
  AchievableInSteps(steps, k) &&
  forall s | 1 <= s < steps :: !AchievableInSteps(s, k)
}

// --- Implementation ---

method Gcd(a: int, b: int) returns (r: int)
  requires a > 0 && b > 0
  ensures IsGcd(r, a, b)
{
  var x := a;
  var y := b;
  while y != 0
  {
    var tmp := y;
    y := x % y;
    x := tmp;
  }
  r := x;
}

method PotionMaking(k: int) returns (steps: int)
  requires 1 <= k <= 100
  ensures IsMinSteps(steps, k)
{
  var g := Gcd(k, 100);
  steps := 100 / g;
}

method Main()
{
  var r: int;

  // ========== SPEC POSITIVE TESTS ==========
  // IsMinSteps(expected_steps, k) should hold for correct pairs

  // From Test 1
  expect IsMinSteps(100, 3), "spec positive: k=3, steps=100";
  expect IsMinSteps(1, 100), "spec positive: k=100, steps=1";
  expect IsMinSteps(4, 25), "spec positive: k=25, steps=4";

  // From Test 4
  expect IsMinSteps(100, 1), "spec positive: k=1, steps=100";

  // From Test 5
  expect IsMinSteps(2, 50), "spec positive: k=50, steps=2";

  // From Test 7
  expect IsMinSteps(50, 2), "spec positive: k=2, steps=50";
  expect IsMinSteps(25, 4), "spec positive: k=4, steps=25";
  expect IsMinSteps(20, 5), "spec positive: k=5, steps=20";

  // From Test 8
  expect IsMinSteps(10, 10), "spec positive: k=10, steps=10";
  expect IsMinSteps(5, 20), "spec positive: k=20, steps=5";
  expect IsMinSteps(10, 30), "spec positive: k=30, steps=10";

  // From Test 9
  expect IsMinSteps(4, 75), "spec positive: k=75, steps=4";

  // From Test 10
  expect IsMinSteps(100, 33), "spec positive: k=33, steps=100";
  expect IsMinSteps(100, 67), "spec positive: k=67, steps=100";
  expect IsMinSteps(100, 99), "spec positive: k=99, steps=100";

  // From Test 11
  expect IsMinSteps(100, 7), "spec positive: k=7, steps=100";
  expect IsMinSteps(100, 13), "spec positive: k=13, steps=100";

  // From Test 12
  expect IsMinSteps(10, 90), "spec positive: k=90, steps=10";

  // From Test 13
  expect IsMinSteps(25, 44), "spec positive: k=44, steps=25";
  expect IsMinSteps(20, 55), "spec positive: k=55, steps=20";
  expect IsMinSteps(50, 66), "spec positive: k=66, steps=50";

  // ========== SPEC NEGATIVE TESTS ==========
  // IsMinSteps(wrong_steps, k) should NOT hold for wrong outputs

  // Neg 1: k=3, wrong=101 (correct=100)
  expect !IsMinSteps(101, 3), "spec negative 1: k=3, wrong=101";

  // Neg 2: k=2, wrong=51 (correct=50)
  expect !IsMinSteps(51, 2), "spec negative 2: k=2, wrong=51";

  // Neg 3: k=7, wrong=101 (correct=100)
  expect !IsMinSteps(101, 7), "spec negative 3: k=7, wrong=101";

  // Neg 4: k=1, wrong=101 (correct=100)
  expect !IsMinSteps(101, 1), "spec negative 4: k=1, wrong=101";

  // Neg 5: k=50, wrong=3 (correct=2)
  expect !IsMinSteps(3, 50), "spec negative 5: k=50, wrong=3";

  // Neg 6: k=100, wrong=2 (correct=1)
  expect !IsMinSteps(2, 100), "spec negative 6: k=100, wrong=2";

  // Neg 7: k=1, wrong=101 (same as Neg 4, included for completeness)
  expect !IsMinSteps(101, 1), "spec negative 7: k=1, wrong=101";

  // Neg 8: k=10, wrong=11 (correct=10)
  expect !IsMinSteps(11, 10), "spec negative 8: k=10, wrong=11";

  // Neg 9: k=25, wrong=5 (correct=4)
  expect !IsMinSteps(5, 25), "spec negative 9: k=25, wrong=5";

  // Neg 10: k=1, wrong=101 (same as Neg 4)
  expect !IsMinSteps(101, 1), "spec negative 10: k=1, wrong=101";

  // ========== IMPLEMENTATION TESTS ==========

  // Test 1
  r := PotionMaking(3);
  expect r == 100, "impl test 1: k=3";
  r := PotionMaking(100);
  expect r == 1, "impl test 1: k=100";
  r := PotionMaking(25);
  expect r == 4, "impl test 1: k=25";

  // Test 2 (100 cases)
  var t2inputs: seq<int> := [
    2, 36, 43, 19, 99, 100, 98, 9, 79, 57,
    1, 78, 56, 14, 66, 93, 62, 50, 76, 33,
    25, 41, 15, 61, 97, 68, 51, 91, 95, 96,
    83, 53, 12, 77, 75, 85, 37, 72, 82, 70,
    44, 69, 58, 52, 48, 73, 21, 24, 20, 8,
    31, 32, 45, 55, 29, 13, 28, 49, 60, 54,
    90, 86, 94, 10, 71, 47, 40, 74, 80, 23,
    26, 84, 38, 89, 4, 39, 6, 22, 92, 46,
    88, 67, 35, 18, 34, 5, 59, 81, 64, 17,
    3, 42, 65, 87, 11, 27, 7, 30, 16, 63
  ];
  var t2expected: seq<int> := [
    50, 25, 100, 100, 100, 1, 50, 100, 100, 100,
    100, 50, 25, 50, 50, 100, 50, 2, 25, 100,
    4, 100, 20, 100, 100, 25, 100, 100, 20, 25,
    100, 100, 25, 100, 4, 20, 100, 25, 50, 10,
    25, 100, 50, 25, 25, 100, 100, 25, 5, 25,
    100, 25, 20, 20, 100, 100, 25, 100, 5, 50,
    10, 50, 50, 10, 100, 100, 5, 50, 5, 100,
    50, 25, 50, 100, 25, 100, 50, 50, 25, 50,
    25, 100, 20, 50, 50, 20, 100, 100, 25, 100,
    100, 50, 20, 100, 100, 100, 100, 10, 25, 100
  ];
  var i := 0;
  while i < |t2inputs| {
    r := PotionMaking(t2inputs[i]);
    expect r == t2expected[i], "impl test 2 failed";
    i := i + 1;
  }

  // Test 3 (100 cases: alternating k=7 and k=3, all expect 100)
  i := 0;
  while i < 50 {
    r := PotionMaking(7);
    expect r == 100, "impl test 3: k=7";
    r := PotionMaking(3);
    expect r == 100, "impl test 3: k=3";
    i := i + 1;
  }

  // Test 4
  r := PotionMaking(1);
  expect r == 100, "impl test 4: k=1";

  // Test 5
  r := PotionMaking(50);
  expect r == 2, "impl test 5: k=50";

  // Test 6
  r := PotionMaking(100);
  expect r == 1, "impl test 6: k=100";

  // Test 7
  r := PotionMaking(1);
  expect r == 100, "impl test 7: k=1";
  r := PotionMaking(2);
  expect r == 50, "impl test 7: k=2";
  r := PotionMaking(3);
  expect r == 100, "impl test 7: k=3";
  r := PotionMaking(4);
  expect r == 25, "impl test 7: k=4";
  r := PotionMaking(5);
  expect r == 20, "impl test 7: k=5";

  // Test 8
  r := PotionMaking(10);
  expect r == 10, "impl test 8: k=10";
  r := PotionMaking(20);
  expect r == 5, "impl test 8: k=20";
  r := PotionMaking(30);
  expect r == 10, "impl test 8: k=30";

  // Test 9
  r := PotionMaking(25);
  expect r == 4, "impl test 9: k=25";
  r := PotionMaking(50);
  expect r == 2, "impl test 9: k=50";
  r := PotionMaking(75);
  expect r == 4, "impl test 9: k=75";
  r := PotionMaking(100);
  expect r == 1, "impl test 9: k=100";

  // Test 10
  r := PotionMaking(1);
  expect r == 100, "impl test 10: k=1";
  r := PotionMaking(33);
  expect r == 100, "impl test 10: k=33";
  r := PotionMaking(50);
  expect r == 2, "impl test 10: k=50";
  r := PotionMaking(67);
  expect r == 100, "impl test 10: k=67";
  r := PotionMaking(99);
  expect r == 100, "impl test 10: k=99";
  r := PotionMaking(100);
  expect r == 1, "impl test 10: k=100";

  // Test 11
  r := PotionMaking(7);
  expect r == 100, "impl test 11: k=7";
  r := PotionMaking(13);
  expect r == 100, "impl test 11: k=13";

  // Test 12
  r := PotionMaking(1);
  expect r == 100, "impl test 12: k=1";
  r := PotionMaking(10);
  expect r == 10, "impl test 12: k=10";
  r := PotionMaking(20);
  expect r == 5, "impl test 12: k=20";
  r := PotionMaking(25);
  expect r == 4, "impl test 12: k=25";
  r := PotionMaking(33);
  expect r == 100, "impl test 12: k=33";
  r := PotionMaking(50);
  expect r == 2, "impl test 12: k=50";
  r := PotionMaking(67);
  expect r == 100, "impl test 12: k=67";
  r := PotionMaking(75);
  expect r == 4, "impl test 12: k=75";
  r := PotionMaking(90);
  expect r == 10, "impl test 12: k=90";
  r := PotionMaking(100);
  expect r == 1, "impl test 12: k=100";

  // Test 13
  r := PotionMaking(44);
  expect r == 25, "impl test 13: k=44";
  r := PotionMaking(55);
  expect r == 20, "impl test 13: k=55";
  r := PotionMaking(66);
  expect r == 50, "impl test 13: k=66";

  print "All tests passed\n";
}