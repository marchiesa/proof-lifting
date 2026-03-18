predicate IsComposite(x: int)
{
  x > 1 && exists d | 2 <= d <= x - 1 :: x % d == 0
}

method Equation(n: int) returns (a: int, b: int)
  requires n >= 1
  ensures IsComposite(a)
  ensures IsComposite(b)
  ensures a - b == n
{
  a := n * 9;
  b := n * 8;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Ensures: IsComposite(a) && IsComposite(b) && a - b == n
  // Small inputs only to keep bounded quantifier in IsComposite fast
  expect IsComposite(9) && IsComposite(8) && 9 - 8 == 1, "spec positive 1";       // n=1
  expect IsComposite(18) && IsComposite(16) && 18 - 16 == 2, "spec positive 4";    // n=2
  expect IsComposite(27) && IsComposite(24) && 27 - 24 == 3, "spec positive 5";    // n=3
  expect IsComposite(36) && IsComposite(32) && 36 - 32 == 4, "spec positive 6";    // n=4
  expect IsComposite(54) && IsComposite(48) && 54 - 48 == 6, "spec positive 8";    // n=6
  expect IsComposite(63) && IsComposite(56) && 63 - 56 == 7, "spec positive 9";    // n=7
  expect IsComposite(72) && IsComposite(64) && 72 - 64 == 8, "spec positive 10";   // n=8

  // === SPEC NEGATIVE TESTS ===
  // Wrong outputs must be rejected by the ensures spec
  expect !(IsComposite(10) && IsComposite(8) && 10 - 8 == 1), "spec negative 1";    // n=1, wrong a=10
  expect !(IsComposite(19) && IsComposite(16) && 19 - 16 == 2), "spec negative 4";  // n=2, wrong a=19
  expect !(IsComposite(28) && IsComposite(24) && 28 - 24 == 3), "spec negative 5";  // n=3, wrong a=28
  expect !(IsComposite(37) && IsComposite(32) && 37 - 32 == 4), "spec negative 6";  // n=4, wrong a=37
  expect !(IsComposite(55) && IsComposite(48) && 55 - 48 == 6), "spec negative 8";  // n=6, wrong a=55
  expect !(IsComposite(64) && IsComposite(56) && 64 - 56 == 7), "spec negative 9";  // n=7, wrong a=64
  expect !(IsComposite(73) && IsComposite(64) && 73 - 64 == 8), "spec negative 10"; // n=8, wrong a=73

  // === IMPLEMENTATION TESTS ===
  var a: int, b: int;

  a, b := Equation(1);
  expect a == 9 && b == 8, "impl test 1 failed";

  a, b := Equation(512);
  expect a == 4608 && b == 4096, "impl test 2 failed";

  a, b := Equation(10000000);
  expect a == 90000000 && b == 80000000, "impl test 3 failed";

  a, b := Equation(2);
  expect a == 18 && b == 16, "impl test 4 failed";

  a, b := Equation(3);
  expect a == 27 && b == 24, "impl test 5 failed";

  a, b := Equation(4);
  expect a == 36 && b == 32, "impl test 6 failed";

  a, b := Equation(8958020);
  expect a == 80622180 && b == 71664160, "impl test 7 failed";

  a, b := Equation(6);
  expect a == 54 && b == 48, "impl test 8 failed";

  a, b := Equation(7);
  expect a == 63 && b == 56, "impl test 9 failed";

  a, b := Equation(8);
  expect a == 72 && b == 64, "impl test 10 failed";

  print "All tests passed\n";
}