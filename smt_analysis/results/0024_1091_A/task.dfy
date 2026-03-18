ghost predicate Beautiful(ny: int, nb: int, nr: int)
{
  nb == ny + 1 && nr == nb + 1
}

ghost predicate ValidChoice(y: int, b: int, r: int, ny: int, nb: int, nr: int)
{
  0 <= ny <= y && 0 <= nb <= b && 0 <= nr <= r && Beautiful(ny, nb, nr)
}

method MaxOrnaments(y: int, b: int, r: int) returns (total: int)
  requires y >= 1 && b >= 2 && r >= 3
  ensures exists ny | 0 <= ny <= y ::
    ValidChoice(y, b, r, ny, ny + 1, ny + 2) &&
    total == ny + (ny + 1) + (ny + 2)
  ensures forall ny | 0 <= ny <= y ::
    ValidChoice(y, b, r, ny, ny + 1, ny + 2) ==>
    ny + (ny + 1) + (ny + 2) <= total
{
  var m := y;
  if b - 1 < m { m := b - 1; }
  if r - 2 < m { m := r - 2; }
  total := 3 * m + 3;
}