ghost predicate IsComposite(x: int)
{
  x > 1 && exists d | 2 <= d <= x - 1 :: x % d == 0
}

method M(n: int) returns (r: int)
  requires n >= 1
  ensures IsComposite(r)
{
  r := n * 9;
  assert r % 3 == 0;
}
