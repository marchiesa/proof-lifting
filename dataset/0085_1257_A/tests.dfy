// --- Specification ---

function Abs(x: int): int
{
  if x >= 0 then x else -x
}

predicate OrderFlipped(a: int, b: int, pa: int, pb: int)
{
  (a < b && pa > pb) || (a > b && pa < pb)
}

function SwapCost(a: int, b: int, pa: int, pb: int): int
{
  Abs(a - pa) + Abs(b - pb) - (if OrderFlipped(a, b, pa, pb) then 1 else 0)
}

predicate IsAchievable(n: int, x: int, a: int, b: int, d: int)
  requires n >= 2 && 1 <= a <= n && 1 <= b <= n && a != b && x >= 0
{
  exists pa: int, pb: int | 1 <= pa <= n && 1 <= pb <= n ::
    pa != pb && Abs(pa - pb) == d && SwapCost(a, b, pa, pb) <= x
}

predicate IsMaxDistance(n: int, x: int, a: int, b: int, d: int)
  requires n >= 2 && 1 <= a <= n && 1 <= b <= n && a != b && x >= 0
{
  IsAchievable(n, x, a, b, d) &&
  forall pa: int, pb: int | 1 <= pa <= n && 1 <= pb <= n ::
    (pa != pb && SwapCost(a, b, pa, pb) <= x) ==> Abs(pa - pb) <= d
}

// --- Implementation ---

method TwoRivalStudents(n: int, x: int, a: int, b: int) returns (distance: int)
  requires n >= 2 && 1 <= a <= n && 1 <= b <= n && a != b && x >= 0
  ensures IsMaxDistance(n, x, a, b, distance)
{
  var la := a;
  var lb := b;
  var rx := x;
  if la > lb {
    var tmp := la;
    la := lb;
    lb := tmp;
  }
  var da := if la - 1 < rx then la - 1 else rx;
  la := la - da;
  rx := rx - da;
  var db := if n - lb < rx then n - lb else rx;
  lb := lb + db;
  distance := lb - la;
}

method Main()
{
  var result: int;

  // === SPEC POSITIVE TESTS ===
  // (small n only so bounded quantifiers are fast to enumerate)
  expect IsMaxDistance(5, 1, 3, 2, 2), "spec positive 1";   // Test 1.1
  expect IsMaxDistance(6, 0, 2, 3, 1), "spec positive 2";   // Test 1.3
  expect IsMaxDistance(2, 0, 1, 2, 1), "spec positive 3";   // Test 2.5
  expect IsMaxDistance(2, 100, 1, 2, 1), "spec positive 4"; // Test 2.6
  expect IsMaxDistance(2, 0, 2, 1, 1), "spec positive 5";   // Test 2.7
  expect IsMaxDistance(2, 100, 2, 1, 1), "spec positive 6"; // Test 2.8
  expect IsMaxDistance(5, 2, 3, 2, 3), "spec positive 7";   // Test 4.1
  expect IsMaxDistance(5, 1, 1, 2, 2), "spec positive 8";   // Test 3 scaled (n=59->5)

  // === SPEC NEGATIVE TESTS ===
  // (wrong outputs — spec must reject these)
  expect !IsMaxDistance(5, 1, 3, 2, 3), "spec negative 1";    // Neg 1: wrong=3, correct=2
  expect !IsMaxDistance(4, 100, 4, 1, 4), "spec negative 2";  // Neg 2 scaled (n=100->4): wrong=n
  expect !IsMaxDistance(5, 1, 1, 2, 3), "spec negative 3";    // Neg 3 scaled (n=59->5): wrong=3, correct=2
  expect !IsMaxDistance(5, 2, 3, 2, 4), "spec negative 4";    // Neg 4: wrong=4, correct=3
  expect !IsMaxDistance(4, 1, 3, 2, 3), "spec negative 5";    // Neg 5 scaled (n=53->4): wrong=3, correct=2

  // === IMPLEMENTATION TESTS ===
  // Test 1
  result := TwoRivalStudents(5, 1, 3, 2);
  expect result == 2, "impl test 1.1 failed";
  result := TwoRivalStudents(100, 33, 100, 1);
  expect result == 99, "impl test 1.2 failed";
  result := TwoRivalStudents(6, 0, 2, 3);
  expect result == 1, "impl test 1.3 failed";

  // Test 2
  result := TwoRivalStudents(100, 100, 100, 1);
  expect result == 99, "impl test 2.1 failed";
  result := TwoRivalStudents(100, 100, 1, 100);
  expect result == 99, "impl test 2.2 failed";
  result := TwoRivalStudents(100, 0, 100, 1);
  expect result == 99, "impl test 2.3 failed";
  result := TwoRivalStudents(100, 0, 1, 100);
  expect result == 99, "impl test 2.4 failed";
  result := TwoRivalStudents(2, 0, 1, 2);
  expect result == 1, "impl test 2.5 failed";
  result := TwoRivalStudents(2, 100, 1, 2);
  expect result == 1, "impl test 2.6 failed";
  result := TwoRivalStudents(2, 0, 2, 1);
  expect result == 1, "impl test 2.7 failed";
  result := TwoRivalStudents(2, 100, 2, 1);
  expect result == 1, "impl test 2.8 failed";
  result := TwoRivalStudents(100, 0, 1, 2);
  expect result == 1, "impl test 2.9 failed";
  result := TwoRivalStudents(100, 98, 1, 2);
  expect result == 99, "impl test 2.10 failed";
  result := TwoRivalStudents(100, 97, 1, 2);
  expect result == 98, "impl test 2.11 failed";
  result := TwoRivalStudents(100, 0, 2, 1);
  expect result == 1, "impl test 2.12 failed";
  result := TwoRivalStudents(100, 98, 2, 1);
  expect result == 99, "impl test 2.13 failed";
  result := TwoRivalStudents(100, 97, 2, 1);
  expect result == 98, "impl test 2.14 failed";
  result := TwoRivalStudents(100, 0, 99, 100);
  expect result == 1, "impl test 2.15 failed";
  result := TwoRivalStudents(100, 98, 99, 100);
  expect result == 99, "impl test 2.16 failed";
  result := TwoRivalStudents(100, 97, 99, 100);
  expect result == 98, "impl test 2.17 failed";
  result := TwoRivalStudents(100, 0, 100, 99);
  expect result == 1, "impl test 2.18 failed";
  result := TwoRivalStudents(100, 98, 100, 99);
  expect result == 99, "impl test 2.19 failed";
  result := TwoRivalStudents(100, 97, 100, 99);
  expect result == 98, "impl test 2.20 failed";
  result := TwoRivalStudents(100, 0, 13, 37);
  expect result == 24, "impl test 2.21 failed";
  result := TwoRivalStudents(100, 0, 66, 11);
  expect result == 55, "impl test 2.22 failed";

  // Test 3
  result := TwoRivalStudents(59, 1, 1, 2);
  expect result == 2, "impl test 3.1 failed";

  // Test 4
  result := TwoRivalStudents(5, 2, 3, 2);
  expect result == 3, "impl test 4.1 failed";

  // Test 5
  result := TwoRivalStudents(53, 1, 3, 2);
  expect result == 2, "impl test 5.1 failed";

  print "All tests passed\n";
}