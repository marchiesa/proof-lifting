method M(n: int) returns (r: int)
  requires n >= 1
  ensures r > 1
  ensures exists d | 2 <= d <= r - 1 :: r % d == 0
{
  r := n * 6;
  assert r % 2 == 0; // r is always even since it's 6n
}