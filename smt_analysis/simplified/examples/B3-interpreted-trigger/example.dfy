ghost function Id(x: int): int { x }

method M(n: int)
  ensures exists d {:trigger Id(d)} | d == n + 1 :: d == d
{
  assert Id(n + 1) == n + 1;
}
