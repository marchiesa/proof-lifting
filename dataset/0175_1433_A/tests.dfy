// ========== SPEC FUNCTIONS AND PREDICATES ==========

function NumDigits(n: int): int
  requires n >= 1
  decreases n
{
  if n < 10 then 1 else 1 + NumDigits(n / 10)
}

function RepUnit(k: int): int
  requires 1 <= k <= 4
{
  if k == 1 then 1 else 10 * RepUnit(k - 1) + 1
}

function BoringNum(d: int, k: int): int
  requires 1 <= d <= 9 && 1 <= k <= 4
{
  d * RepUnit(k)
}

predicate IsBoringApartment(x: int)
{
  exists d {:trigger BoringNum(d, 1)} | 1 <= d <= 9 ::
    exists k {:trigger BoringNum(d, k)} | 1 <= k <= 4 :: x == BoringNum(d, k)
}

function TotalKeypresses(d: int, k: int): int
  requires 1 <= d <= 9 && 1 <= k <= 4
  decreases 4 * (d - 1) + (k - 1)
{
  var cost := NumDigits(BoringNum(d, k));
  if d == 1 && k == 1 then cost
  else if k > 1 then TotalKeypresses(d, k - 1) + cost
  else TotalKeypresses(d - 1, 4) + cost
}

// Top-level ensures predicate extracted for testability
predicate EnsuresBoringApartments(x: int, keypresses: int)
{
  exists d {:trigger BoringNum(d, 1)} | 1 <= d <= 9 ::
    exists k {:trigger BoringNum(d, k)} | 1 <= k <= 4 ::
    x == BoringNum(d, k) && keypresses == TotalKeypresses(d, k)
}

// ========== IMPLEMENTATION ==========

method BoringApartments(x: int) returns (keypresses: int)
  requires IsBoringApartment(x)
  ensures EnsuresBoringApartments(x, keypresses)
{
  var d := x % 10;
  var k := NumDigits(x);
  keypresses := TotalKeypresses(d, k);
}

// ========== TESTS ==========

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Testing the top-level ensures predicate with correct (input, output) pairs
  expect EnsuresBoringApartments(1, 1), "spec positive 1";       // Test 6
  expect EnsuresBoringApartments(22, 13), "spec positive 2";     // Test 5
  expect EnsuresBoringApartments(33, 23), "spec positive 3";     // Test 10
  expect EnsuresBoringApartments(5, 41), "spec positive 4";      // Test 9
  expect EnsuresBoringApartments(777, 66), "spec positive 5";    // Test 8
  expect EnsuresBoringApartments(9999, 90), "spec positive 6";   // Test 7
  expect EnsuresBoringApartments(9, 81), "spec positive 7";      // Test 2
  expect EnsuresBoringApartments(11, 3), "spec positive 8";      // Test 2
  expect EnsuresBoringApartments(4, 31), "spec positive 9";      // Test 2
  expect EnsuresBoringApartments(99, 83), "spec positive 10";    // Test 2

  // === SPEC NEGATIVE TESTS ===
  // Testing the top-level ensures predicate with wrong outputs (must be false)
  expect !EnsuresBoringApartments(1, 2), "spec negative 1";      // Neg 6: correct=1
  expect !EnsuresBoringApartments(22, 14), "spec negative 2";    // Neg 5: correct=13
  expect !EnsuresBoringApartments(33, 24), "spec negative 3";    // Neg 10: correct=23
  expect !EnsuresBoringApartments(5, 42), "spec negative 4";     // Neg 9: correct=41
  expect !EnsuresBoringApartments(9999, 91), "spec negative 5";  // Neg 7: correct=90
  expect !EnsuresBoringApartments(777, 67), "spec negative 6";   // Neg 8: correct=66
  expect !EnsuresBoringApartments(999, 87), "spec negative 7";   // Neg 4: correct=86

  // === IMPLEMENTATION TESTS ===
  // All 36 boring apartments (from Test 2)
  var r: int;

  r := BoringApartments(1);
  expect r == 1, "impl test 1";
  r := BoringApartments(2);
  expect r == 11, "impl test 2";
  r := BoringApartments(3);
  expect r == 21, "impl test 3";
  r := BoringApartments(4);
  expect r == 31, "impl test 4";
  r := BoringApartments(5);
  expect r == 41, "impl test 5";
  r := BoringApartments(6);
  expect r == 51, "impl test 6";
  r := BoringApartments(7);
  expect r == 61, "impl test 7";
  r := BoringApartments(8);
  expect r == 71, "impl test 8";
  r := BoringApartments(9);
  expect r == 81, "impl test 9";
  r := BoringApartments(11);
  expect r == 3, "impl test 10";
  r := BoringApartments(22);
  expect r == 13, "impl test 11";
  r := BoringApartments(33);
  expect r == 23, "impl test 12";
  r := BoringApartments(44);
  expect r == 33, "impl test 13";
  r := BoringApartments(55);
  expect r == 43, "impl test 14";
  r := BoringApartments(66);
  expect r == 53, "impl test 15";
  r := BoringApartments(77);
  expect r == 63, "impl test 16";
  r := BoringApartments(88);
  expect r == 73, "impl test 17";
  r := BoringApartments(99);
  expect r == 83, "impl test 18";
  r := BoringApartments(111);
  expect r == 6, "impl test 19";
  r := BoringApartments(222);
  expect r == 16, "impl test 20";
  r := BoringApartments(333);
  expect r == 26, "impl test 21";
  r := BoringApartments(444);
  expect r == 36, "impl test 22";
  r := BoringApartments(555);
  expect r == 46, "impl test 23";
  r := BoringApartments(666);
  expect r == 56, "impl test 24";
  r := BoringApartments(777);
  expect r == 66, "impl test 25";
  r := BoringApartments(888);
  expect r == 76, "impl test 26";
  r := BoringApartments(999);
  expect r == 86, "impl test 27";
  r := BoringApartments(1111);
  expect r == 10, "impl test 28";
  r := BoringApartments(2222);
  expect r == 20, "impl test 29";
  r := BoringApartments(3333);
  expect r == 30, "impl test 30";
  r := BoringApartments(4444);
  expect r == 40, "impl test 31";
  r := BoringApartments(5555);
  expect r == 50, "impl test 32";
  r := BoringApartments(6666);
  expect r == 60, "impl test 33";
  r := BoringApartments(7777);
  expect r == 70, "impl test 34";
  r := BoringApartments(8888);
  expect r == 80, "impl test 35";
  r := BoringApartments(9999);
  expect r == 90, "impl test 36";

  // Additional implementation tests from Test 4
  r := BoringApartments(999);
  expect r == 86, "impl test 37";
  r := BoringApartments(8888);
  expect r == 80, "impl test 38";
  r := BoringApartments(6666);
  expect r == 60, "impl test 39";
  r := BoringApartments(666);
  expect r == 56, "impl test 40";

  print "All tests passed\n";
}