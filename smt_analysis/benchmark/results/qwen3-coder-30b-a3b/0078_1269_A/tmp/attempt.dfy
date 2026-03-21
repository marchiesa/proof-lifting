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
  b := n * 8;
  
  assert a > 1;
  assert b > 1;
  assert a - b == n;
  
  // Prove IsComposite(a)
  assert a > 1 ==> exists d | 2 <= d <= a - 1 :: a % d == 0;
  assert a % 3 == 0;
  assert 3 >= 2 && 3 <= a - 1;
  
  // Prove IsComposite(b)
  assert b > 1 ==> exists d | 2 <= d <= b - 1 :: b % d == 0;
  assert b % 2 == 0;
  assert 2 >= 2 && 2 <= b - 1;
}