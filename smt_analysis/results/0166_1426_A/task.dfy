// Models the problem structure: which apartments are on which floor.
// Floor 1 contains apartments 1 and 2.
// Floor f (f >= 2) contains x apartments: from (f-2)*x + 3 to (f-1)*x + 2.
ghost predicate ApartmentOnFloor(n: int, x: int, f: int)
{
  if f == 1 then
    1 <= n <= 2
  else
    f >= 2 && (f - 2) * x + 3 <= n <= (f - 1) * x + 2
}

method FloorNumber(n: int, x: int) returns (floor: int)
  requires n >= 1
  requires x >= 1
  ensures ApartmentOnFloor(n, x, floor)
{
  if n <= 2 {
    floor := 1;
  } else {
    var m := n - 3;
    floor := m / x + 2;
  }
}