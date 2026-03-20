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
  a := n * 9;
  assert a > 1;
  assert a % 3 == 0;
  assert 3 <= a - 1;
  b := n * 8;
  assert b > 1;
  assert b % 2 == 0;
  assert 2 <= b - 1;
}