ghost function Abs(x: int): int
{
  if x >= 0 then x else -x
}

// A cell at grid position (x, y) belongs to the n-th order rhombus iff its
// Manhattan distance from the center (0, 0) is less than n. This characterizes
// the shape built by the problem's recursive construction: start with (0,0)
// and repeatedly adjoin all cells sharing a side.
ghost predicate InRhombus(x: int, y: int, n: int)
  requires n >= 1
{
  Abs(x) + Abs(y) <= n - 1
}

// For a given row x at radius r, count the integer y values with |x|+|y| <= r.
ghost function RowWidth(x: int, r: int): int
  requires r >= 0
{
  if Abs(x) > r then 0
  else 2 * (r - Abs(x)) + 1
}

// Sum RowWidth(x, r) for x in [lo .. hi].
ghost function SumRows(lo: int, hi: int, r: int): int
  requires r >= 0
  decreases if lo <= hi then hi - lo + 1 else 0
{
  if lo > hi then 0
  else RowWidth(lo, r) + SumRows(lo + 1, hi, r)
}

// Total cells in the n-th order rhombus: count of (x, y) with |x|+|y| <= n-1.
ghost function RhombusCellCount(n: int): int
  requires n >= 1
{
  SumRows(-(n - 1), n - 1, n - 1)
}

method Rhombus(n: int) returns (cells: int)
  requires n >= 1
  ensures cells == RhombusCellCount(n)
{
  cells := 1;
  var i := 1;
  while i < n
  {
    cells := cells + i * 4;
    i := i + 1;
  }
}