// Whether either variable strictly exceeds the threshold n
ghost predicate Exceeds(a: int, b: int, n: int) {
  a > n || b > n
}

// Whether it is possible to make either variable exceed n starting from (a, b)
// using at most `steps` operations, where each operation is either
// "a += b" (producing (a+b, b)) or "b += a" (producing (a, b+a)).
ghost predicate Reachable(a: int, b: int, n: int, steps: nat)
  decreases steps
{
  Exceeds(a, b, n) ||
  (steps > 0 && (Reachable(a + b, b, n, steps - 1) || Reachable(a, b + a, n, steps - 1)))
}

method CPlusEqual(a: int, b: int, n: int) returns (ops: int)
  requires a > 0 && b > 0 && n > 0
  requires a <= n && b <= n
  ensures ops >= 1 && Reachable(a, b, n, ops) && !Reachable(a, b, n, ops - 1)
{
  var x := a;
  var y := b;
  if x > y {
    x, y := y, x;
  }
  var i := 1;
  while i < 1000 {
    if i % 2 == 1 {
      x := x + y;
    } else {
      y := y + x;
    }
    if x > n || y > n {
      ops := i;
      return;
    }
    i := i + 1;
  }
  ops := 0;
  return;
}