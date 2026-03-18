ghost predicate IsTriangle(x: int, y: int, z: int)
{
  x + y > z && x + z > y && y + z > x
}

ghost predicate CanFormTriangleWithKMinutes(a: int, b: int, c: int, k: int)
{
  k >= 0 &&
  exists da | 0 <= da <= k ::
    exists db | 0 <= db <= k - da ::
      IsTriangle(a + da, b + db, c + (k - da - db))
}

ghost predicate IsMinimalMinutes(a: int, b: int, c: int, minutes: int)
{
  CanFormTriangleWithKMinutes(a, b, c, minutes) &&
  forall k :: 0 <= k < minutes ==> !CanFormTriangleWithKMinutes(a, b, c, k)
}

method MakeTriangle(a: int, b: int, c: int) returns (minutes: int)
  requires a >= 1 && b >= 1 && c >= 1
  ensures minutes >= 0
  ensures IsMinimalMinutes(a, b, c, minutes)
{
  var m := a;
  if b > m { m := b; }
  if c > m { m := c; }
  var diff := m - a - b - c + m + 1;
  if diff < 0 { minutes := 0; } else { minutes := diff; }
}