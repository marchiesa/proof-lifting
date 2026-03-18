ghost function Min(a: int, b: int): int {
  if a <= b then a else b
}

ghost function Max(a: int, b: int): int {
  if a >= b then a else b
}

ghost predicate Divides(d: int, n: int)
  requires d > 0
{
  n % d == 0
}

ghost predicate IsGcd(g: int, a: int, b: int)
  requires a > 0 && b > 0 && g > 0
{
  Divides(g, a) && Divides(g, b) &&
  forall d :: 1 <= d <= Min(a, b) ==> (Divides(d, a) && Divides(d, b)) ==> d <= g
}

ghost predicate IsLcm(l: int, a: int, b: int)
  requires a > 0 && b > 0 && l > 0
{
  Divides(a, l) && Divides(b, l) &&
  forall m :: 1 <= m <= l ==> (Divides(a, m) && Divides(b, m)) ==> l <= m
}

ghost predicate ValidSolution(a: int, b: int, x: int)
{
  a > 0 && b > 0 && x > 0 &&
  exists g | 1 <= g <= Min(a, b) ::
    exists l | Max(a, b) <= l <= a * b ::
      IsGcd(g, a, b) && IsLcm(l, a, b) && g + l == x
}

method EhAbAndGcd(x: int) returns (a: int, b: int)
  requires x >= 2
  ensures ValidSolution(a, b, x)
{
  a := 1;
  b := x - 1;
}