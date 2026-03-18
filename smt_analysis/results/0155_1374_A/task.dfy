ghost predicate InRange(k: int, n: int)
{
  0 <= k <= n
}

ghost predicate HasRemainder(k: int, x: int, y: int)
  requires x > 0
{
  k % x == y
}

ghost predicate IsMaxWithRemainder(k: int, x: int, y: int, n: int)
  requires x > 0
{
  InRange(k, n)
  && HasRemainder(k, x, y)
  && (forall k' :: 0 <= k' <= n ==> HasRemainder(k', x, y) ==> k' <= k)
}

method RequiredRemainder(x: int, y: int, n: int) returns (k: int)
  requires x > 0
  requires 0 <= y < x
  requires y <= n
  ensures IsMaxWithRemainder(k, x, y, n)
{
  var p := n % x;
  if p == y {
    k := n;
  } else if p > y {
    k := n - p + y;
  } else {
    k := n - p - (x - y);
  }
}