ghost function Gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases b
{
  if a % b == 0 then b
  else Gcd(b, a % b)
}

method MaximumGCD(n: int) returns (result: int)
  requires n >= 2
  ensures exists a: int | 1 <= a && a < n :: exists b: int | a < b && b <= n :: Gcd(a, b) == result
  ensures forall a: int | 1 <= a && a < n :: forall b: int | a < b && b <= n :: Gcd(a, b) <= result
{
  result := n / 2;
}