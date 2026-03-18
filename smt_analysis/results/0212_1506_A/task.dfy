// The number assigned to cell (row, col) in column-major ("by columns") numbering:
// columns filled left to right, within each column rows go top to bottom.
ghost function ByColumnsNumber(n: int, row: int, col: int): int
{
  col * n + row + 1
}

// The number assigned to cell (row, col) in row-major ("by rows") numbering:
// rows filled top to bottom, within each row columns go left to right.
ghost function ByRowsNumber(m: int, row: int, col: int): int
{
  row * m + col + 1
}

method StrangeTable(n: int, m: int, x: int) returns (result: int)
  requires n >= 1 && m >= 1
  requires 1 <= x <= n * m
  ensures exists row | 0 <= row < n :: exists col | 0 <= col < m ::
            ByColumnsNumber(n, row, col) == x &&
            result == ByRowsNumber(m, row, col)
{
  var x0 := x - 1;
  var r := x0 / n;
  var c := x0 % n;
  result := c * m + r + 1;
}