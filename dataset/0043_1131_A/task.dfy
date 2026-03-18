// The ship consists of two left-aligned rectangles stacked vertically.
// Bottom rectangle: cells (x, y) with 1 <= x <= w1, 1 <= y <= h1
// Top rectangle:    cells (x, y) with 1 <= x <= w2, h1+1 <= y <= h1+h2
ghost predicate IsShipCell(x: int, y: int, w1: int, h1: int, w2: int, h2: int)
{
  (1 <= x <= w1 && 1 <= y <= h1) ||
  (1 <= x <= w2 && h1 + 1 <= y <= h1 + h2)
}

// A cell is marked if it is NOT part of the ship but is adjacent
// (by side or corner, i.e., Chebyshev distance 1) to at least one ship cell.
ghost predicate IsMarkedCell(x: int, y: int, w1: int, h1: int, w2: int, h2: int)
{
  !IsShipCell(x, y, w1, h1, w2, h2) &&
  exists dx | -1 <= dx <= 1 ::
    exists dy | -1 <= dy <= 1 ::
      !(dx == 0 && dy == 0) && IsShipCell(x + dx, y + dy, w1, h1, w2, h2)
}

// Count marked cells in row y for x in [x..xHi]
ghost function CountMarkedRow(x: int, xHi: int, y: int,
                        w1: int, h1: int, w2: int, h2: int): int
  decreases xHi - x + 1
{
  if x > xHi then 0
  else (if IsMarkedCell(x, y, w1, h1, w2, h2) then 1 else 0)
       + CountMarkedRow(x + 1, xHi, y, w1, h1, w2, h2)
}

// Count marked cells in grid for y in [y..yHi], x in [xLo..xHi]
ghost function CountMarkedGrid(y: int, yHi: int, xLo: int, xHi: int,
                         w1: int, h1: int, w2: int, h2: int): int
  decreases yHi - y + 1
{
  if y > yHi then 0
  else CountMarkedRow(xLo, xHi, y, w1, h1, w2, h2)
       + CountMarkedGrid(y + 1, yHi, xLo, xHi, w1, h1, w2, h2)
}

// All marked cells lie within the bounding box [0, w1+1] x [0, h1+h2+1].
ghost function TotalMarked(w1: int, h1: int, w2: int, h2: int): int
  requires w1 >= 1 && h1 >= 1 && w2 >= 1 && h2 >= 1 && w1 >= w2
{
  CountMarkedGrid(0, h1 + h2 + 1, 0, w1 + 1, w1, h1, w2, h2)
}

method SeaBattle(w1: int, h1: int, w2: int, h2: int) returns (marked: int)
  requires w1 >= 1 && h1 >= 1 && w2 >= 1 && h2 >= 1 && w1 >= w2
  ensures marked == TotalMarked(w1, h1, w2, h2)
{
  marked := (w1 + 2) * (h1 + h2 + 2) - (w1 - w2) * h2 - w1 * h1 - w2 * h2;
}