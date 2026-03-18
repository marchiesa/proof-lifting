ghost function GCD(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures GCD(a, b) > 0
  decreases b
{
  if b == 0 then a else GCD(b, a % b)
}

ghost function LCM(a: int, b: int): int
  requires a > 0 && b > 0
{
  (a / GCD(a, b)) * b
}

ghost predicate ValidPair(x: int, y: int, l: int, r: int)
  requires l >= 1
{
  l <= x && x < y && y <= r && l <= LCM(x, y) && LCM(x, y) <= r
}

ghost predicate PairExists(l: int, r: int)
  requires l >= 1
{
  exists x | l <= x <= r :: exists y | x + 1 <= y <= r :: ValidPair(x, y, l, r)
}

method LCMProblem(l: int, r: int) returns (x: int, y: int)
  requires l >= 1
  ensures (x == -1 && y == -1) || ValidPair(x, y, l, r)
  ensures (x == -1 && y == -1) <==> !PairExists(l, r)
{
  if l * 2 > r {
    return -1, -1;
  } else {
    return l, l * 2;
  }
}