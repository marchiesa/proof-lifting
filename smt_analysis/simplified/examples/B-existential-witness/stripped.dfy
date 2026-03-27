ghost predicate P(x: int, y: int)
{ x > 0 && y == x * 2 }

method M(n: int) returns (r: int)
  requires n >= 1
  ensures exists x :: P(x, r)
{
  r := n * 2;
// TODO: add assertion here
}
