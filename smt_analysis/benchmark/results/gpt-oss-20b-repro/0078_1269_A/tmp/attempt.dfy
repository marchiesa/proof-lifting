ghost predicate IsComposite(x: int)
{
  x > 1 && exists d | 2 <= d <= x - 1 :: x % d == 0
}

method Equation(n: int) returns (a: int, b: int)
  requires n >= 1
  ensures IsComposite(a)
  ensures IsComposite(b)
  ensures a - b == n
{
  // Choose a and b such that a - b = n
  // Let a = 9 * n, b = 8 * n
  // We need to prove 9*n and 8*n are composite for n >= 1

  a := n * 9;
  b := n * 8;

  assert a - b == n; // difference holds
  assert a > 1; // since n >= 1, a = 9*n >= 9 > 1
  assert b > 1; // since n >= 1, b = 8*n >= 8 > 1

  // Show a is composite: a = 9*n = 3 * (3*n)
  assert a % 3 == 0; // because a = 9*n divisible by 3
  assert 2 <= 3 <= a - 1; // 3 is in [2, a-1]
  assert a % 3 == 0; // reassert for IsComposite
  assert IsComposite(a); // composite by divisor 3

  // Show b is composite: b = 8*n = 4 * (2*n)
  assert b % 4 == 0; // divisible by 4
  assert 2 <= 4 <= b - 1; // 4 is in [2, b-1]
  assert b % 4 == 0; // reassert for IsComposite
  assert IsComposite(b); // composite by divisor 4
}