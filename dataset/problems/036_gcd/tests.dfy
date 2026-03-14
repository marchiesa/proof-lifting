// Compute GCD (Euclidean Algorithm) -- Test cases

function GcdFunc(a: nat, b: nat): nat
  decreases b
{
  if b == 0 then a
  else GcdFunc(b, a % b)
}

method {:axiom} Gcd(a: int, b: int) returns (g: int)
  requires a > 0 && b > 0
  ensures g == GcdFunc(a, b)
  ensures g > 0

method TestGcd12_8()
{
  var g := Gcd(12, 8);
  assert GcdFunc(12, 8) == GcdFunc(8, 4) == GcdFunc(4, 0) == 4;
  assert g == 4;
}

method TestGcdEqual()
{
  var g := Gcd(7, 7);
  assert GcdFunc(7, 7) == GcdFunc(7, 0) == 7;
  assert g == 7;
}

method TestGcdCoprime()
{
  var g := Gcd(3, 5);
  assert GcdFunc(3, 5) == GcdFunc(5, 3) == GcdFunc(3, 2) == GcdFunc(2, 1) == GcdFunc(1, 0) == 1;
  assert g == 1;
}
