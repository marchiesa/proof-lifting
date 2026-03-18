ghost predicate IsValidWindow(a: int, b: int, c1: int, r1: int, c2: int, r2: int)
{
  0 <= c1 <= c2 < a && 0 <= r1 <= r2 < b
}

ghost predicate WindowAvoidsDead(c1: int, r1: int, c2: int, r2: int, x: int, y: int)
{
  x < c1 || x > c2 || y < r1 || y > r2
}

ghost function WindowArea(c1: int, r1: int, c2: int, r2: int): int
{
  (c2 - c1 + 1) * (r2 - r1 + 1)
}

method DeadPixel(a: int, b: int, x: int, y: int) returns (area: int)
  requires a >= 1 && b >= 1
  requires 0 <= x < a && 0 <= y < b
  ensures area >= 0
  // Optimality: no valid window avoiding the dead pixel has area greater than the result
  ensures forall c1, r1, c2, r2 ::
    (0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b &&
    IsValidWindow(a, b, c1, r1, c2, r2) && WindowAvoidsDead(c1, r1, c2, r2, x, y))
      ==> WindowArea(c1, r1, c2, r2) <= area
  // Achievability: the result is either 0 (no valid window) or achieved by some valid window
  ensures area == 0 ||
    (exists c1, r1, c2, r2 | 0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b ::
      IsValidWindow(a, b, c1, r1, c2, r2) && WindowAvoidsDead(c1, r1, c2, r2, x, y) &&
      WindowArea(c1, r1, c2, r2) == area)
{
  var v1 := x * b;
  var v2 := y * a;
  var v3 := (a - x - 1) * b;
  var v4 := (b - y - 1) * a;
  area := v1;
  if v2 > area { area := v2; }
  if v3 > area { area := v3; }
  if v4 > area { area := v4; }
  return;
}