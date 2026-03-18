// --- Specification: model the problem's structure ---

function BitwiseXor(a: int, b: int): int
  requires a >= 0 && b >= 0
  decreases a + b
{
  if a == 0 && b == 0 then 0
  else (if a % 2 != b % 2 then 1 else 0) + 2 * BitwiseXor(a / 2, b / 2)
}

function XorwiceObjective(a: int, b: int, x: int): int
  requires a >= 0 && b >= 0 && x >= 0
{
  BitwiseXor(a, x) + BitwiseXor(b, x)
}

predicate IsMinimumXorwice(a: int, b: int, result: int)
  requires a >= 0 && b >= 0
{
  (exists x | 0 <= x <= a + b :: result == XorwiceObjective(a, b, x))
  &&
  (forall x | 0 <= x <= a + b :: result <= XorwiceObjective(a, b, x))
}

// --- Method with specification ---

method XORwice(a: int, b: int) returns (result: int)
  requires a >= 0 && b >= 0
  ensures IsMinimumXorwice(a, b, result)
{
  var x := a;
  var y := b;
  if x < y {
    x := b;
    y := a;
  }
  var z := 0;
  var tX := x;
  var tY := y;
  var bit := 1;
  while tX > 0 || tY > 0
    decreases tX + tY
  {
    if tX % 2 == 1 && tY % 2 == 1 {
      z := z + bit;
    }
    tX := tX / 2;
    tY := tY / 2;
    bit := bit * 2;
  }
  var axz := 0;
  tX := x;
  var tZ := z;
  bit := 1;
  while tX > 0 || tZ > 0
    decreases tX + tZ
  {
    if tX % 2 != tZ % 2 {
      axz := axz + bit;
    }
    tX := tX / 2;
    tZ := tZ / 2;
    bit := bit * 2;
  }
  var bxz := 0;
  tY := y;
  tZ := z;
  bit := 1;
  while tY > 0 || tZ > 0
    decreases tY + tZ
  {
    if tY % 2 != tZ % 2 {
      bxz := bxz + bit;
    }
    tY := tY / 2;
    tZ := tZ / 2;
    bit := bit * 2;
  }
  result := axz + bxz;
}

method Main()
{
  var r: int;

  // =============================================
  // SPEC POSITIVE TESTS (small inputs only)
  // =============================================
  expect IsMinimumXorwice(1, 1, 0), "spec positive 1";    // test 2: (1,1)->0
  expect IsMinimumXorwice(2, 3, 1), "spec positive 2";    // test 3: (2,3)->1
  expect IsMinimumXorwice(7, 7, 0), "spec positive 3";    // test 4: (7,7)->0
  expect IsMinimumXorwice(1, 2, 3), "spec positive 4";    // test 10: (1,2)->3
  expect IsMinimumXorwice(5, 5, 0), "spec positive 5";    // test 10: (5,5)->0
  expect IsMinimumXorwice(15, 8, 7), "spec positive 6";   // test 6: (15,8)->7
  expect IsMinimumXorwice(10, 20, 30), "spec positive 7"; // test 5: (10,20)->30

  // =============================================
  // SPEC NEGATIVE TESTS (small inputs only)
  // =============================================
  expect !IsMinimumXorwice(1, 1, 1), "spec negative 1";    // neg 2: wrong=1, correct=0
  expect !IsMinimumXorwice(2, 3, 2), "spec negative 2";    // neg 3: wrong=2, correct=1
  expect !IsMinimumXorwice(7, 7, 1), "spec negative 3";    // neg 4: wrong=1, correct=0
  expect !IsMinimumXorwice(1, 2, 4), "spec negative 4";    // neg 10: wrong=4, correct=3
  expect !IsMinimumXorwice(6, 12, 11), "spec negative 5";  // neg 1: wrong=11, correct=10
  expect !IsMinimumXorwice(15, 8, 8), "spec negative 6";   // neg 6: wrong=8, correct=7
  expect !IsMinimumXorwice(10, 20, 31), "spec negative 7"; // neg 5: wrong=31, correct=30

  // =============================================
  // IMPLEMENTATION TESTS (full-size inputs)
  // =============================================
  // Test 1
  r := XORwice(6, 12);
  expect r == 10, "impl test 1a";
  r := XORwice(4, 9);
  expect r == 13, "impl test 1b";
  r := XORwice(59, 832);
  expect r == 891, "impl test 1c";
  r := XORwice(28, 14);
  expect r == 18, "impl test 1d";
  r := XORwice(4925, 2912);
  expect r == 6237, "impl test 1e";
  r := XORwice(1, 1);
  expect r == 0, "impl test 1f";

  // Test 2
  r := XORwice(1, 1);
  expect r == 0, "impl test 2";

  // Test 3
  r := XORwice(2, 3);
  expect r == 1, "impl test 3";

  // Test 4
  r := XORwice(7, 7);
  expect r == 0, "impl test 4";

  // Test 5
  r := XORwice(10, 20);
  expect r == 30, "impl test 5";

  // Test 6
  r := XORwice(15, 8);
  expect r == 7, "impl test 6";

  // Test 7
  r := XORwice(3, 50);
  expect r == 49, "impl test 7";

  // Test 8
  r := XORwice(48, 49);
  expect r == 1, "impl test 8";

  // Test 9
  r := XORwice(25, 30);
  expect r == 7, "impl test 9";

  // Test 10
  r := XORwice(1, 2);
  expect r == 3, "impl test 10a";
  r := XORwice(5, 5);
  expect r == 0, "impl test 10b";
  r := XORwice(12, 7);
  expect r == 11, "impl test 10c";

  // Test 11
  r := XORwice(33, 44);
  expect r == 13, "impl test 11a";
  r := XORwice(50, 50);
  expect r == 0, "impl test 11b";

  print "All tests passed\n";
}