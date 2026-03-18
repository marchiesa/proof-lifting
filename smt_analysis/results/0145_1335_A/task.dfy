ghost predicate ValidDistribution(n: int, a: int, b: int) {
  a > 0 && b > 0 && a > b && a + b == n
}

ghost function CountDistributions(n: int, hi: int): int
  requires hi >= 0
  decreases hi
{
  if hi < 1 then 0
  else CountDistributions(n, hi - 1) + (if ValidDistribution(n, n - hi, hi) then 1 else 0)
}

method Candies(n: int) returns (ways: int)
  requires n >= 1
  ensures ways == CountDistributions(n, n - 1)
{
  if n <= 2 {
    ways := 0;
  } else {
    ways := (n - 1) / 2;
  }
}