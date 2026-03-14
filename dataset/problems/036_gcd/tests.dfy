// Compute GCD (Euclidean Algorithm) -- Runtime spec tests

function GcdFunc(a: nat, b: nat): nat
  decreases b
{
  if b == 0 then a
  else GcdFunc(b, a % b)
}

method Main() {
  // Known GCD values
  expect GcdFunc(12, 8) == 4, "gcd(12,8) = 4";
  expect GcdFunc(7, 7) == 7, "gcd(7,7) = 7";
  expect GcdFunc(3, 5) == 1, "gcd(3,5) = 1 (coprime)";
  expect GcdFunc(100, 25) == 25, "gcd(100,25) = 25";
  expect GcdFunc(48, 18) == 6, "gcd(48,18) = 6";
  expect GcdFunc(1, 1) == 1, "gcd(1,1) = 1";
  expect GcdFunc(17, 1) == 1, "gcd(17,1) = 1";

  // Wrong answer checks
  expect GcdFunc(12, 8) != 2, "gcd(12,8) is not 2";
  expect GcdFunc(12, 8) != 8, "gcd(12,8) is not 8";

  // Base case
  expect GcdFunc(5, 0) == 5, "gcd(5,0) = 5";
  expect GcdFunc(0, 0) == 0, "gcd(0,0) = 0";

  print "All spec tests passed\n";
}
