// Checks whether a specific allocation of grapes satisfies all constraints:
//   ga/gd/gm = green grapes to Andrew/Dmitry/Michal
//   pd/pm    = purple grapes to Dmitry/Michal
//   bm       = black grapes to Michal
// Andrew eats only green; Dmitry eats green or purple; Michal eats any type.
ghost predicate ValidAllocation(x: int, y: int, z: int, a: int, b: int, c: int,
                          ga: int, gd: int, pd: int, gm: int, pm: int, bm: int)
{
  ga >= 0 && gd >= 0 && pd >= 0 && gm >= 0 && pm >= 0 && bm >= 0 &&
  ga >= x &&
  gd + pd >= y &&
  gm + pm + bm >= z &&
  ga + gd + gm <= a &&
  pd + pm <= b &&
  bm <= c
}

// There exists a distribution of grapes making everyone happy.
// We fix Andrew's share at exactly x green (giving more wastes green grapes).
// We search over gd: how many green grapes Dmitry receives.
// Dmitry's purple share is y - gd; Michal receives all remaining grapes.
ghost predicate Feasible(x: int, y: int, z: int, a: int, b: int, c: int)
  requires x >= 0 && y >= 0 && z >= 0 && a >= 0 && b >= 0 && c >= 0
{
  var bound := if a - x < y then a - x else y;
  exists gd: int | 0 <= gd <= bound ::
    ValidAllocation(x, y, z, a, b, c,
                    x, gd, y - gd, a - x - gd, b - (y - gd), c)
}

method GotAnyGrapes(x: int, y: int, z: int, a: int, b: int, c: int) returns (result: bool)
  requires x >= 0 && y >= 0 && z >= 0 && a >= 0 && b >= 0 && c >= 0
  ensures result == Feasible(x, y, z, a, b, c)
{
  var a' := a;
  var b' := b;
  var c' := c;

  c' := c' - z;
  if c' < 0 {
    b' := b' + c';
  }
  b' := b' - y;
  if b' < 0 {
    a' := a' + b';
  }
  a' := a' - x;

  result := a' >= 0;
}