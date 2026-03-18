ghost predicate ValidDistribution(a: int, b: int, c: int, n: int, A: int, B: int, C: int)
{
  A >= 0 && B >= 0 && C >= 0
  && A + B + C == n
  && a + A == b + B
  && a + A == c + C
}

ghost predicate CanDistribute(a: int, b: int, c: int, n: int)
  requires n >= 0
{
  exists A: int, B: int, C: int
    :: ValidDistribution(a, b, c, n, A, B, C)
}

method CollectingCoins(a: int, b: int, c: int, n: int) returns (result: bool)
  requires a >= 0 && b >= 0 && c >= 0 && n >= 0
  ensures result == CanDistribute(a, b, c, n)
{
  var tot := a + b + c + n;
  if tot % 3 != 0 {
    return false;
  }
  var des := tot / 3;
  if a > des || b > des || c > des {
    return false;
  }
  return true;
}